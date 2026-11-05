-- Prove2me | Theorems.Thm_DegenNRM_theorem_1
-- name    : DegenNRM.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:37:33.999123+00:00
-- url     : https://prove2.me/theorems/48ea4211-da2a-4bd7-bba8-a76c5f08436b
-- title:
--   Theorem 1 — Algorithm 1 with Algorithm 2 has regret $\le((2\kappa_1+2)/\alpha+(4/\alpha)\sum_j1/p_j)\log^2T+s_0r_{\max}$
-- statement:
--   There is a function $S(n,\kappa,p)$ of the number of types $n$, a real $\kappa$ and a vector $p\in\mathbb R^n$ such that the following holds. Let an instance with $m$ resources and $n$ types satisfy Assumption 1 with constant $\alpha$, let $C\ge0$ be the initial capacities and $T$ the number of periods, and let $\pi$ be Algorithm 1 with the estimator $\hat M$ of Algorithm 2 and the constant $\kappa_1$ of (15), using any selection of optimal solutions of (13). Then $V^{\mathrm{off}}(I)$ and $V^\pi(I)$ are integrable and
--   $$\mathrm{Regret}(\pi)\le\Big(\frac{2\kappa_1+2}{\alpha}+\frac4\alpha\sum_{j=1}^n\frac1{p_j}\Big)\log^2T+s_0\,r_{\max},$$
--   where $s_0=S(n,\kappa_1,p)$ depends only on $\kappa_1$, $n$ and $\{p_j\}$, and $r_{\max}=\max_ju_j$.
--
--   This is the main result of the paper: a $O(\log^2T)$ regret for network revenue management with continuous reward distributions, with no non-degeneracy assumption on the fluid program.
--
--   **Formalization Note** The function $S$ is chosen before the instance, $\alpha$, $C$, $T$ and the selection, so $s_0$ is uniform in everything but $(n,\kappa_1,p)$. The statement covers every $m$, $n$, every $T$ (for $T\le1$ the bound is $s_0r_{\max}$) and point-mass reward laws.
--
--   Differences from the source:
--
--   - encoding: m resources, n query types; query t has size ã_t ∈ A = {a_1,…,a_n} and reward r̃_t, and the type j_t is observed → resources Fin m, types Fin n; an arrival is (j, r) ∈ Fin n × ℝ with size a_j, the law of an arrival is Σ_j p_j (δ_j ⊗ F_j), and periods t ∈ [T] are the coordinates t − 1 of a path in (Fin n × ℝ)^T; reason: reading R3 of the mission (Algorithm 2 takes the type j_t as input, p.15); same instances
--   - encoding: p_j = P(ã = a_j) for the support A = {a_1,…,a_n} → p_j > 0 and Σ_j p_j = 1; reason: a support point has positive probability and κ₁ of (15) divides by p_j; this excludes only undefined cases
--   - reading: Assumption 1: F_j supported on [l_j, u_j] with density f(·|a_j) ≥ α; l_j = u_j allowed, with 'density ∞' so that any α > 0 qualifies (p.10) → α > 0 and, for every j, F_j([l_j, u_j]) = 1 and either l_j = u_j or F_j = Lebesgue·f_j with f_j(r) ≥ α on [l_j, u_j]; reason: the printed hypothesis with its point-mass convention made explicit (reading R4)
--   - reading: F_j⁻¹, the inverse distribution function (not defined in the paper) → F_j⁻¹(q) = inf{r ∈ [l_j, u_j] : F_j((−∞, r]) ≥ q}; reason: the standard generalized inverse, restricted to the reward interval (reading R5)
--   - reading: κ₁ = max_j{1/p_j}·(m + 2n)·āⁿ with ā not defined → ā = max_j (‖a_j‖₂² + 2)^{1/2}; reason: reading R1: the largest column norm of [A; I_n; −I_n], which the proof of Lemma 4 (p.43) bounds; the alternative max_j ‖a_j‖₂ makes Lemma 4 false (m = 1, n = 2, a = (0.01, 0), p = (1/2, 1/2), U[0,1] rewards, c = 0.4, s = 100, d = (40, 60))
--   - encoding: log → Real.log (natural logarithm; log 0 = log 1 = 0); reason: the paper's log is natural (Hoeffding step, p.16)
--   - reading: 'Obtain {q̂*_{j,t}} by solving the optimization problem (13)' (Algorithm 2, line 2) → every selection σ(t, c) of optimal solutions of (13) at s = T − t + 1, for t ∈ [T] and c ≥ 0; reason: (13) can have several optima and the paper does not say which is used (reading R5)
--   - reading: 's₀ is a constant that depends on κ₁, n and {p_j}' → ∃ S : (n : ℕ) → ℝ → (Fin n → ℝ) → ℝ, quantified before the instance, with s₀ = S n κ₁ p; reason: reading R2, the strongest reading of the sentence; every condition on s₀ in the proof (pp.16–18) involves only n, κ₁ and p
--   - encoding: Algorithm 2's three tests 'if … else if … else if' with the third condition 2κ₁√(log s/s) ≤ q̂* ≤ 1 − 2κ₁√(log s/s) → if … else if … else; reason: the third condition holds whenever the first two fail, so the branches are the same
--   - generalization: Regret(π) bounded for a model with T periods and m resources → the bound for every T ∈ ℕ and m ∈ ℕ, together with the integrability of V^off and V^π; reason: T = 0 or m = 0 are degenerate instances of the same statement; dropping the integrability conjuncts gives the printed bound
-- source:
--   Jiang, Ma & Zhang, Degeneracy is OK: Logarithmic Regret for Network Revenue Management with Indiscrete Distributions, arXiv:2210.07996v5, Theorem 1, p.15; proof pp.15–18

import Mathlib
import Definitions.Def_DegenNRM_Assumption1
import Definitions.Def_DegenNRM_policyRun

open MeasureTheory

namespace DegenNRM

/-- **Theorem 1: Algorithm 1 with the estimator of Algorithm 2 has `O(log² T)` regret**
(Jiang, Ma & Zhang, *Degeneracy is OK: Logarithmic Regret for Network Revenue Management with
Indiscrete Distributions*, arXiv:2210.07996v5, Theorem 1, p.15).

Denote by `π` Algorithm 1 with the estimator `M̂` of Algorithm 2 and the constant `κ₁` of (15).
There is a constant `s₀ = S(n, κ₁, {p_j})` depending only on `n`, `κ₁` and `{p_j}` such that, for
every instance satisfying Assumption 1 with density bound `α`, every initial capacity `C ≥ 0`,
every horizon `T` and every selection of optimal solutions of (13) used by Algorithm 2,

`Regret(π) ≤ ((2κ₁ + 2)/α + (4/α) Σ_{j=1}^n 1/p_j) · log² T + s₀ · r_max`,

where `r_max = max_j u_j`.

**Formalization Note.** `s₀` is uniform (reading R2): the function `S` is chosen before
`m`, `n`, the instance, `α`, `C`, `T` and the selection, and `s₀ = S n κ₁ p`. `κ₁ = kappa1 inst`
is (15) with `ā = max_j (‖a_j‖₂² + 2)^{1/2}` (reading R1); it is also the constant inside
Algorithm 2. The selection `σ` ranges over all optimal solutions of (13) (`IsFluidSelection`,
reading R5). `log` is the natural logarithm. The two integrability conjuncts make the Bochner
integrals in `regret` the expectations of (3). -/
theorem theorem_1 :
    ∃ S : (n : ℕ) → ℝ → (Fin n → ℝ) → ℝ,
      ∀ (m n : ℕ) (inst : Instance m n) (α : ℝ), Assumption1 inst α →
        ∀ (C : Fin m → ℝ), 0 ≤ C → ∀ (T : ℕ) (σ : ℕ → (Fin m → ℝ) → (Fin n → ℝ)),
          IsFluidSelection inst T σ →
          Integrable (offlineValue inst C) (pathLaw inst T) ∧
            Integrable (policyValue inst C σ) (pathLaw inst T) ∧
            regret inst C T σ ≤
              ((2 * kappa1 inst + 2) / α + 4 / α * ∑ j, 1 / inst.p j) * Real.log T ^ 2
                + S n (kappa1 inst) inst.p * rmax inst := by sorry

end DegenNRM
