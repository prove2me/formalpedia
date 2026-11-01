-- Prove2me | Theorems.Thm_FocusSetRB_theorem_5
-- name    : FocusSetRB.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:20:26.374392+00:00
-- url     : https://prove2.me/theorems/659e224c-a649-42fc-965b-9d75c6ea5040
-- title:
--   Theorem 5, eq. (18), p.14 — meta-theorem on the optimality gap of focus-set policies
-- statement:
--   Let $y^*$ be an optimal solution of (LP) whose policy $\bar\pi^*$ induces an aperiodic unichain (Assumption 1), let $0<\alpha<1$, $N\ge1$ and $k=\alpha N\in\mathbb N$. Let $\pi$ be a focus-set policy (Algorithm 1) with any update kernel, any rectifier obeying (4)–(5), any initial state vector $S_0$ and any initial focus set $D_{-1}$. Let $\{h(\cdot,D)\}_{D\in\mathcal D}$ be subset Lyapunov functions (Definition 1) with constants $\rho_2,K_{\mathrm{drift}},K_{\mathrm{dist}},L_h$, with $[N]\in\mathcal D$, and let $K_{\mathrm{conf}},K_{\mathrm{mono}},L_{\mathrm{cov}},K_{\mathrm{cov}}>0$. Suppose that at every pair $(x,D)$ that $(X_t,D_t)$ takes with positive probability for some $t$:
--
--   1. $D\in\mathcal D$;
--   2. (Condition 1) there is a choice of $D'_t\subseteq D_t$, $D'_t\in\mathcal D$, depending on the realized $(\hat A_t,A_t)$, with $A_t(i)=\hat A_t(i)$ for $i\in D'_t$, such that $\mathbb E[m(D_t\setminus D'_t)\mid X_t,D_t]\le K_{\mathrm{conf}}/\sqrt N$;
--   3. (Condition 2) $D_{t+1}\supseteq D_t$ or $D_{t+1}\subseteq D_t$, and $\mathbb E[(m(D_t)-m(D_{t+1}))^+\mid X_t,D_t]\le K_{\mathrm{mono}}/\sqrt N$;
--   4. (Condition 3) $1-m(D_t)\le L_{\mathrm{cov}}\,h(X_t,D_t)+K_{\mathrm{cov}}/\sqrt N$.
--
--   Then
--
--   $$
--   R^*(N,S_0)-R^-(\pi,S_0)\le r_{\max}\left(\Big(\frac1{K_{\mathrm{dist}}}+\frac2{L_h}\Big)\frac{K_1}{1-\rho_1}+2K_{\mathrm{conf}}\right)\frac1{\sqrt N},
--   $$
--
--   where $\rho_1=1-(1-\rho_2)/(1+L_hL_{\mathrm{cov}})$ and $K_1=K_{\mathrm{drift}}+2L_hK_{\mathrm{conf}}+2L_hK_{\mathrm{mono}}+(1-\rho_2)L_hK_{\mathrm{cov}}/(1+L_hL_{\mathrm{cov}})$.
--
--   Every focus-set policy whose focus set covers most arms, conforms to $\bar\pi^*$ on most of them and almost never shrinks is $O(1/\sqrt N)$-optimal; Theorems 1 and 2 of the paper are obtained by checking the three conditions.
--
--   Differences from the source:
--   - reading: R(π, S₀), the long-run average reward → R⁻(π, S₀), the liminf average reward; reason: p.5 defines the optimality gap as R*(N,S₀) − R⁻(π,S₀) and writes R(π,S₀) for it when the limit exists; R⁻ is always defined and equals R where the limit exists
--   - encoding: R*(N,S₀) the optimal value of (RB) over policies that may be randomized and use the whole history → supremum of R⁻ over history-dependent randomized policies whose every action vector pulls exactly k = αN arms; reason: the class the paper describes on p.5; the budget (1a) holds at every step
--   - reading: Conditions 1–3 hold "a.s." for any time step → they hold at every pair (x, D) that (X_t, D_t) takes with positive probability for some t; reason: the process is a finite Markov chain, so "almost surely at every time" means at every pair of positive probability
--   - reading: there exists D′_t ⊆ D_t with A_t(i) = Â_t(i) for i ∈ D′_t (Condition 1) → a function D′ = Dsub(Â, A) ⊆ D_t, with A = Â on it and D′ ∈ 𝒟, on every (Â, A) of positive probability; reason: the proof (p.16) evaluates h(·, D′_t), which Definition 1 provides only on 𝒟, and applies (14) between D′_t and D_t, so D′_t ∈ 𝒟 is what the page's h requires; the ID policy's D′_t is a prefix in its 𝒟 of prefixes (Section 7), not the largest conforming set; for 𝒟 = all subsets the largest conforming set qualifies; a function of (Â, A) loses nothing, since the largest admissible member of 𝒟 is one
--   - reading: a class of subset Lyapunov functions {h(·, D)}_{D∈𝒟} for which the conditions hold → also every D_t of positive probability lies in 𝒟, and [N] ∈ 𝒟; reason: the conditions evaluate h(X_t, D_t) and the proof ((19)–(21)) evaluates h(X_t, [N]) and uses Lipschitz continuity between D_t and [N]; both are needed for the statement to be about the policy, and both hold when 𝒟 is all subsets
--   - generalization: constants independent of N, bound for all N and S₀ → the statement for one N, with constants allowed to depend on that N; reason: applying it at every N with N-independent constants gives the paper's statement
--   - generalization: a focus-set policy of Algorithm 1 (actions off D_t chosen "based on X_t and D_t") → any rectifier kernel obeying (4)–(5), which may also use the ideal actions of all arms; reason: contains Algorithm 1's rectifiers; Algorithm 2 (lines 14–15) uses the ideal actions off D_t
--   - encoding: A₀(i) ∼ π̄*(·|S₀(i)) for i ∈ D, the actions of the other arms unspecified → the other arms take arbitrary actions aOut, quantified over every choice; reason: the quantity depends only on the arms of D, whose next states depend only on their own actions, so every law of the other actions gives the same expectation
--   - encoding: μ* is the stationary distribution of P_π̄* → μ*(s) := y*(s,0) + y*(s,1); reason: the paper states this identity on p.7; it is stationary by (2b) and (3) and is the unique stationary law under Assumption 1, so the same vector
--   - encoding: αN an integer, N arms → k : ℕ with (k : ℝ) = α·N and N ≥ 1; reason: the paper assumes αN is an integer (p.5); an N-armed problem has N ≥ 1
--   - encoding: P_π̄* induces an aperiodic unichain (a single recurrent class and a possibly empty set of transient states) → some state is recurrent, any two recurrent states reach each other, and every recurrent state has period 1; transient states are unconstrained; reason: the same property of a finite chain spelled out state by state; the period of a state is the gcd of its return times
--   - reading: D_t chosen based on X_t and D_{t−1}, actions based on X_t and D_t (Algorithm 1), "any set" in Algorithm 2 → the update and the rectifier are fixed kernels that do not depend on t; reason: Algorithm 1 names those as the inputs of the rule, and Appendix D (p.40) treats (S_t, A_t, X_t, D_t) as a finite-state Markov chain
--   - encoding: arms indexed by [N] = {1,…,N} → arms indexed by Fin N = {0,…,N−1}; reason: relabelling only
-- source:
--   Hong, Xie, Chen, Wang, Unichain and Aperiodicity are Sufficient for Asymptotic Optimality of Average-Reward Restless Bandits, arXiv:2402.05689v4, Theorem 5, eq. (18), p.14; Definition 1, p.13; Conditions 1–3, pp.13–14

import Mathlib
import Definitions.Def_FocusSetRB_LPFeasible
import Definitions.Def_FocusSetRB_IsAperiodicUnichain
import Definitions.Def_FocusSetRB_focusLaw
import Definitions.Def_FocusSetRB_IsSubsetLyapunov

namespace FocusSetRB

/-- **Theorem 5 (Meta-theorem on optimality gap of focus-set policies), eq. (18), p.14**
(Hong, Xie, Chen, Wang, arXiv:2402.05689v4). Consider an `N`-armed restless bandit with single-armed MDP `(𝕊, 𝔸, P, r)` and budget
`αN`, `0 < α < 1`, under Assumption 1. Let `π` be a focus-set policy (Algorithm 1) satisfying
Conditions 1, 2 and 3 (pp.13–14) for a class of subset Lyapunov functions `{h(·, D)}_{D ∈ 𝒟}`
(Definition 1). Then
`R*(N, S₀) − R(π, S₀) ≤ r_max ((1/K_dist + 2/L_h) K₁/(1 − ρ₁) + 2K_conf) (1/√N)`,
where `ρ₁ = 1 − (1 − ρ₂)/(1 + L_h L_cov)` and
`K₁ = K_drift + 2L_h K_conf + 2L_h K_mono + (1 − ρ₂) L_h K_cov/(1 + L_h L_cov)`.

Here `y` is an optimal solution of (LP) whose policy `π̄*` (3) induces an aperiodic unichain
(Assumption 1, p.7, the paper's standing assumption). The focus-set policy is any update kernel `sel` (line 2), the ideal actions of
line 3, any rectifier obeying (4)–(5) (`IsRectifier`, lines 4–5) and any initial focus set
`Dinit = D_{−1}`.

**Formalization Note.** `R(π, S₀)` is the liminf average reward `R⁻(π, S₀)` (the source's
optimality gap, p.5); `R*` is the supremum of `R⁻` over history-dependent randomized policies.
The conditions are required at every pair `(x, D)` that `(X_t, D_t)` takes with positive
probability for some `t` (`IsChargedPair`), which is the source's "a.s. for any time step":
* Condition 1 (15): `D'_t ⊆ D_t` is a function `Dsub` of the realized `(Â_t, A_t)`, with
  `A_t(i) = Â_t(i)` on `D'_t` and `D'_t ∈ 𝒟` (the proof, p.16, evaluates `h(·, D'_t)`, which
  Definition 1 only provides on `𝒟`, and applies (14) between `D'_t` and `D_t`);
* Condition 2 (16), with "`D_{t+1} ⊇ D_t` or `D_{t+1} ⊆ D_t`" for every next focus set of positive
  probability;
* Condition 3 (17);
* every focus set `D_t` of positive probability lies in `𝒟`, and `[N] ∈ 𝒟` (the conditions evaluate
  `h(X_t, D_t)`, and the proof uses `h(·, [N])`).
The constants are fixed for the given `N`. -/
theorem theorem_5 {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (M : SingleArmMDP S) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {y : S → Bool → ℝ} (hy : IsLPOptimal M α y) (hU : IsAperiodicUnichain (Ppi M y))
    {N k : ℕ} (hN : 1 ≤ N) (hk : (k : ℝ) = α * N) (S0 : Fin N → S) (Dinit : Finset (Fin N))
    (sel : (Fin N → S) → Finset (Fin N) → Finset (Fin N) → ℝ) (hsel : IsSelectorKernel sel)
    (rect : (Fin N → S) → Finset (Fin N) → (Fin N → Bool) → (Fin N → Bool) → ℝ)
    (hrect : IsRectifier k rect)
    (𝒟 : Set (Finset (Fin N))) (h : (Fin N → S) → Finset (Fin N) → ℝ)
    (ρ₂ Kdrift Kdist Lh Kconf Kmono Lcov Kcov : ℝ)
    (hLyap : IsSubsetLyapunov M y 𝒟 h ρ₂ Kdrift Kdist Lh)
    (huniv : (Finset.univ : Finset (Fin N)) ∈ 𝒟)
    (hKconf : 0 < Kconf) (hKmono : 0 < Kmono) (hLcov : 0 < Lcov) (hKcov : 0 < Kcov)
    (hmem : ∀ x D, IsChargedPair M y sel rect S0 Dinit x D → D ∈ 𝒟)
    (hC1 : ∀ x D, IsChargedPair M y sel rect S0 Dinit x D →
      ∃ Dsub : (Fin N → Bool) → (Fin N → Bool) → Finset (Fin N),
        (∀ Ahat A, 0 < idealLaw y x Ahat → 0 < rect x D Ahat A →
          Dsub Ahat A ⊆ D ∧ Dsub Ahat A ∈ 𝒟 ∧ ∀ i ∈ Dsub Ahat A, A i = Ahat i) ∧
        ∑ Ahat, idealLaw y x Ahat *
            ∑ A, rect x D Ahat A * frac (D \ Dsub Ahat A) ≤
          Kconf / Real.sqrt N)
    (hC2 : ∀ x D, IsChargedPair M y sel rect S0 Dinit x D →
      (∀ Ahat A x' D', 0 < idealLaw y x Ahat → 0 < rect x D Ahat A → 0 < stepProb M x A x' →
          0 < sel x' D D' → D ⊆ D' ∨ D' ⊆ D) ∧
      ∑ Ahat, idealLaw y x Ahat * ∑ A, rect x D Ahat A *
          ∑ x', stepProb M x A x' * ∑ D', sel x' D D' * max (frac D - frac D') 0 ≤
        Kmono / Real.sqrt N)
    (hC3 : ∀ x D, IsChargedPair M y sel rect S0 Dinit x D →
      1 - frac D ≤ Lcov * h x D + Kcov / Real.sqrt N) :
    Rstar M N k S0 - focusRminus M y sel rect S0 Dinit ≤
      rmax M * ((1 / Kdist + 2 / Lh) *
          ((Kdrift + 2 * Lh * Kconf + 2 * Lh * Kmono +
              (1 - ρ₂) * Lh * Kcov / (1 + Lh * Lcov)) /
            (1 - (1 - (1 - ρ₂) / (1 + Lh * Lcov)))) + 2 * Kconf) * (1 / Real.sqrt N) := by sorry

end FocusSetRB
