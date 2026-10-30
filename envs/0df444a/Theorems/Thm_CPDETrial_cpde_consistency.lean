-- Prove2me | Theorems.Thm_CPDETrial_cpde_consistency
-- name    : CPDETrial.cpde_consistency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:24:29.582+00:00
-- url     : https://prove2.me/theorems/939b8781-7540-4bf9-b6c0-67dc0c80b300
-- title:
--   Theorem 1 — asymptotic consistency of the cPDE allocation policy
-- statement:
--   Let $M\ge2$ arms have unknown means $\theta\sim N(\mu^0,\Sigma^0)$ and observations $Y^t_i\mid\theta\sim N(\theta_i,\lambda_i)$, independent given $\theta$, and suppose Assumption 1 holds:
--
--   1. $\mu^0$, $\Sigma^0$ and $\Lambda=\mathrm{diag}(\lambda_1,\dots,\lambda_M)$ are known;
--   2. $\Sigma^0$ and $\Lambda$ are positive definite;
--   3. $\mathbb P\{\lim_{T\to\infty}\sum_{t=1}^T\mathbf 1\{j\in\mathcal M_t\}=\infty\}=1$ for each arm $j$;
--   4. $\Delta=1$ and $c_j>0$ for each arm $j$.
--
--   Let the allocation be nonanticipating and, at every time $t$, choose an arm of the consideration set $\mathcal M_t$ that maximizes the cPDE index $\nu^*_j(\mu^t,\Sigma^t)$ (eq. (EC.8)) over $\mathcal M_t$, ties broken by any nonanticipating rule. Then, for every arm $i$:
--
--   1. $\lim_{T\to\infty}\Sigma^T_{i,i}=0$ almost surely;
--   2. $\lim_{T\to\infty}\nu^*_i(\mu^T,\Sigma^T)=-1$ almost surely;
--   3. $\lim_{T\to\infty}\mu^T_i=\theta_i$ almost surely and in $L^2$;
--   4. almost surely, $\theta$ has a unique best arm $i^*$, and $i^*$ is the unique maximizer of $\mu^T$ for all large $T$:
--   $$
--   \lim_{T\to\infty}\arg\max_i\{\mu^T_i\}=\arg\max_i\{\theta_i\}.
--   $$
--
--   So a trial that allocates patients by the cPDE index learns every arm's mean and eventually identifies the best arm.
--
--   **Formalization Note** Prices and fixed costs are normalized ($P=1$, $I_j=0$, as in §3.2 of the paper), and Assumption 1(i) has no formal content: the prior and sampling variances are fixed parameters.
--
--   Differences from the source:
--   - reading: three formulas for ν* ((15) p. 11, (20) p. 12, (EC.8) p. ec3); p. 12 refers to '(19)' → ν* is (EC.8) with Δ = 1, as `nuStar`; reason: (EC.8) is the index the proof of Theorem 1 uses; (15) lacks −(1/c_i) max_j µ_j, with which Theorem 1(ii) fails; (20) agrees with (EC.8) only for deterministic T; '(19)' is the stopping index, a typo for (20); 'setting Δ = 0' on p. ec3 is a typo for Δ = 1
--   - reading: sup over T_i ≥ 1 for policies sampling only arm i → sup over stopping times T ≥ 1 of the natural filtration of Z with T < ∞ a.s., E[T] < ∞ and integrable payoff; reason: these are the policies of Π_i; a stopping time with E[T] = ∞ has value −∞ and does not attain the supremum
--   - generalization: cPDE allocates to an arm maximizing ν* over M (p. 11), ties broken randomly; §3.3 allows consideration sets M_t ⊆ M → any allocation that maximizes ν* over arbitrary random consideration sets M_t satisfying Assumption 1(iii), ties broken by any nonanticipating rule; reason: M_t = M with uniform random tie-breaking is an instance (App. B.10: cPDE includes all arms in every M_t); no measurability of M_t is assumed
--   - generalization: nonanticipating policies H_t → M (p. 7) → allocations measurable in H_t ∨ 𝓖 for an external σ-algebra 𝓖 independent of (θ, ε); reason: covers random tie-breaking and random consideration sets; taking 𝓖 trivial gives the paper's policies
--   - reading: lim_{T→∞} ν*_i(µ^t,Σ^t) → lim_{T→∞} ν*_i(µ^T,Σ^T); reason: the limit variable is T; µ^t is a typo
--   - reading: iv) lim_{T→∞} arg max{µ^T_i} = arg max{θ_i} almost surely for each i → almost surely θ has a unique maximizer i, and eventually i is the unique maximizer of µ^T; reason: the argmax lives in a finite set, so the limit is eventual equality; uniqueness is asserted in the proof (p. ec7); 'for each i' has no content
--   - encoding: Y^t_i | θ_i ∼ N(θ_i, λ_i), independent given θ → Y^t_i = θ_i + ε^t_i, errors independent N(0, λ_i) independent of θ; reason: same joint law
--   - encoding: convergence in L² → eLpNorm (µ^T_i − θ_i) 2 P → 0; reason: Mathlib's L² norm; same notion
-- source:
--   Chick, Gans & Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN preprint 3184758 (version of August 31, 2020), p. 13, Theorem 1 under Assumption 1 (proof pp. ec3–ec7, App. B.4)

import Mathlib
import Definitions.Def_CPDETrial_muT
import Definitions.Def_CPDETrial_SigT
import Definitions.Def_CPDETrial_nuStar
import Definitions.Def_CPDETrial_TrialModel
import Definitions.Def_CPDETrial_IsNonanticipating
import Definitions.Def_CPDETrial_IsCPDEAllocation
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace CPDETrial

/-- **Theorem 1 — asymptotic consistency of the cPDE allocation policy.**
Chick, Gans & Yapar, *Bayesian Sequential Learning for Clinical Trials of Multiple Correlated
Medical Interventions*, SSRN preprint 3184758 (version of August 31, 2020), Theorem 1, p. 13, under Assumption 1 (p. 13):
"Assumption 1. i) `µ⁰`, `Σ⁰` and `Λ` are known. ii) `Σ⁰` and `Λ` are positive definite.
iii) `P{lim_{T→∞} Σ_{t=1}^T 1{j ∈ M_t} = ∞} = 1` for each `j ∈ M`. iv) `Δ = 1` and `c_j > 0` for
each `j ∈ M`."
"Theorem 1. Suppose Assumption 1 holds. Then i) `lim_{T→∞} Σ^T_{i,i} = 0` almost surely for each
`i`; ii) `lim_{T→∞} ν*_i(µ^t,Σ^t) = −1` almost surely for each `i`; iii) `lim_{T→∞} µ^T_i = θ_i`
almost surely and in `L²` for each `i`; and iv) `lim_{T→∞} arg max{µ^T_i} = arg max{θ_i}` almost
surely for each `i`."

Setting: `M ≥ 2` arms; `θ ∼ N(µ⁰, Σ⁰)` with `Σ⁰` positive definite; observations
`Y^t_i = θ_i + ε^t_i` with independent `N(0, λ_i)` errors, `λ_i > 0`; costs `c_j > 0`; `P = 1`,
`I_j = 0`, `Δ = 1` (built into `nuStar`). The allocation `u` is nonanticipating (it may also use
external randomness `𝓖` independent of `θ` and the errors), and at every time `t` allocates an
arm of the consideration set `M_t = Mset t` that maximizes the cPDE index `ν*` (EC.8) over `M_t`
at the current posterior. Every arm belongs to `M_t` for infinitely many `t`, almost surely.
Then, for every arm `i`:
1. `Σ^T_{ii} → 0` almost surely;
2. `ν*_i(µ^T, Σ^T) → −1` almost surely;
3. `µ^T_i → θ_i` almost surely and in `L²`;
4. almost surely, `θ` has a unique maximizing arm `i*`, and from some time on `i*` is the unique
   maximizer of `µ^T`.

**Formalization Note.** Assumption 1(i) has no formal content: `µ⁰, Σ⁰, Λ` are fixed parameters.
`ν*` is (EC.8) (see `nuStar`). The page's "`ν*_i(µ^t,Σ^t)`" under `lim_{T→∞}` is read as
`ν*_i(µ^T,Σ^T)`. Clause (iv) is read as eventual equality of the (unique) arg max sets, its
"for each `i`" having no content. Ties in the arg max over `M_t` may be broken by any
nonanticipating rule (uniformly random tie-breaking is one instance), and `M_t` may be any
random consideration sets satisfying Assumption 1(iii); `M_t = M` is the cPDE policy of p. 11.
`L²` convergence is `eLpNorm (µ^T_i − θ_i) 2 P → 0`. -/
theorem cpde_consistency {M : ℕ} (hM : 2 ≤ M) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (mu0 : Fin M → ℝ)
    (Sig0 : Matrix (Fin M) (Fin M) ℝ) (hSig0 : Sig0.PosDef)
    (lam : Fin M → ℝ≥0) (hlam : ∀ i, 0 < lam i) (c : Fin M → ℝ) (hc : ∀ j, 0 < c j)
    (θ : Ω → EuclideanSpace ℝ (Fin M)) (ε : ℕ → Fin M → Ω → ℝ) (𝓖 : MeasurableSpace Ω)
    (u : ℕ → Ω → Fin M) (Mset : ℕ → Ω → Finset (Fin M))
    (hmodel : TrialModel P mu0 Sig0 lam θ ε 𝓖)
    (hna : IsNonanticipating 𝓖 θ ε u)
    (hcpde : IsCPDEAllocation mu0 Sig0 lam c θ ε u Mset)
    (hA1iii : ∀ j, ∀ᵐ ω ∂P, {t | j ∈ Mset t ω}.Infinite) :
    (∀ i, ∀ᵐ ω ∂P, Tendsto (fun T => SigT Sig0 lam u T ω i i) atTop (𝓝 0)) ∧
    (∀ i, ∀ᵐ ω ∂P, Tendsto (fun T => nuStar c lam i (muT mu0 Sig0 lam θ ε u T ω)
        (SigT Sig0 lam u T ω)) atTop (𝓝 (-1))) ∧
    (∀ i, (∀ᵐ ω ∂P, Tendsto (fun T => muT mu0 Sig0 lam θ ε u T ω i) atTop (𝓝 (θ ω i))) ∧
      Tendsto (fun T => eLpNorm (fun ω => muT mu0 Sig0 lam θ ε u T ω i - θ ω i) 2 P)
        atTop (𝓝 0)) ∧
    (∀ᵐ ω ∂P, ∃ i, (∀ j, j ≠ i → θ ω j < θ ω i) ∧
      ∀ᶠ T in atTop, ∀ j, j ≠ i → muT mu0 Sig0 lam θ ε u T ω j < muT mu0 Sig0 lam θ ε u T ω i) := by sorry

end CPDETrial
