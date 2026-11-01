-- Prove2me | Theorems.Thm_FocusSetRB_lemma_5
-- name    : FocusSetRB.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:21:48.244977+00:00
-- url     : https://prove2.me/theorems/9d80491b-6ccd-4ca8-b2cc-53b1e333179d
-- title:
--   Lemma 5, eq. (38), p.18 — the set-expansion policy satisfies Condition 3
-- statement:
--   Let $y^*$ be an optimal solution of (LP) whose policy $\bar\pi^*$ induces an aperiodic unichain (Assumption 1), let $0<\alpha<1$, $\beta=\min\{\alpha,1-\alpha\}$ and $N\ge1$. Consider a focus-set update obeying Algorithm 2, lines 2–5. For every system state $x$, every previous focus set $D_{\mathrm{prev}}$ and every focus set $D$ the update can choose from $(x,D_{\mathrm{prev}})$,
--
--   $$
--   1-m(D)\le\frac{|\mathbb S|^{1/2}}{\beta}\,h_W(x,D)+\frac{2}{\beta N}.
--   $$
--
--   In the paper's words, $1-m(D_t)\le(|\mathbb S|^{1/2}/\beta)\,h_W(X_t,D_t)+2/(\beta N)$ almost surely: the focus set covers enough arms relative to the Lyapunov function (Condition 3, sufficient coverage).
--
--   Differences from the source:
--   - generalization: the set-expansion policy of Algorithm 2 ("any set with the largest m(D_t)") → every update kernel whose possible outputs obey lines 2–5; reason: contains every choice of maximizer in lines 3 and 5
--   - generalization: a.s., for the time-t pair (X_t, D_t) of the policy started at D_{−1} = ∅ → for every state x, every previous focus set D_prev and every D the update can choose from (x, D_prev); reason: every pair (X_t, D_t) of positive probability is of this form, so the pointwise bound implies the a.s. bound
--   - encoding: μ* is the stationary distribution of P_π̄* → μ*(s) := y*(s,0) + y*(s,1); reason: the paper states this identity on p.7; it is stationary by (2b) and (3) and is the unique stationary law under Assumption 1, so the same vector
--   - encoding: arms indexed by [N] = {1,…,N} → arms indexed by Fin N = {0,…,N−1}; reason: relabelling only
--   - encoding: P_π̄* induces an aperiodic unichain (a single recurrent class and a possibly empty set of transient states) → some state is recurrent, any two recurrent states reach each other, and every recurrent state has period 1; transient states are unconstrained; reason: the same property of a finite chain spelled out state by state; the period of a state is the gcd of its return times
--   - encoding: W = ∑_{k≥0} (P_π̄* − Ξ)^k (P_π̄*ᵀ − Ξᵀ)^k → a tsum in Matrix S S ℝ with the entrywise topology; reason: the series converges under Assumption 1 (Lemma 11), so the tsum is its sum
--   - reading: D_t chosen based on X_t and D_{t−1}, actions based on X_t and D_t (Algorithm 1), "any set" in Algorithm 2 → the update and the rectifier are fixed kernels that do not depend on t; reason: Algorithm 1 names those as the inputs of the rule, and Appendix D (p.40) treats (S_t, A_t, X_t, D_t) as a finite-state Markov chain
-- source:
--   Hong, Xie, Chen, Wang, Unichain and Aperiodicity are Sufficient for Asymptotic Optimality of Average-Reward Restless Bandits, arXiv:2402.05689v4, Lemma 5, eq. (38), p.18

import Mathlib
import Definitions.Def_FocusSetRB_LPFeasible
import Definitions.Def_FocusSetRB_IsAperiodicUnichain
import Definitions.Def_FocusSetRB_IsSetExpansionSelector

namespace FocusSetRB

/-- **Lemma 5 (Set-expansion policy satisfies Condition 3), eq. (38), p.18** (Hong, Xie, Chen, Wang, arXiv:2402.05689v4).
Consider the set-expansion policy in Algorithm 2. For any `t ≥ 0`,
`1 − m(D_t) ≤ (|𝕊|^{1/2}/β) h_W(X_t, D_t) + 2/(βN)` a.s., with `β = min{α, 1 − α}`.

Here `y` is an optimal solution of (LP) whose policy `π̄*` (3) induces an aperiodic unichain
(Assumption 1, p.7, the paper's standing assumption).

**Formalization Note.** The inequality is proved for every state `x`, every previous focus set
`Dprev` and every `D` that the set-expansion update (Algorithm 2, lines 2–5,
`IsSetExpansionSelector`) can choose from `(x, Dprev)`, which contains every `(X_t, D_t)` of
positive probability. Arms are `Fin N`, `N ≥ 1`. -/
theorem lemma_5 {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (M : SingleArmMDP S) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {y : S → Bool → ℝ} (hy : IsLPOptimal M α y) (hU : IsAperiodicUnichain (Ppi M y))
    {N : ℕ} (hN : 1 ≤ N)
    (sel : (Fin N → S) → Finset (Fin N) → Finset (Fin N) → ℝ)
    (hsel : IsSetExpansionSelector α y sel)
    (x : Fin N → S) (Dprev D : Finset (Fin N)) (hD : 0 < sel x Dprev D) :
    1 - frac D ≤ Real.sqrt (Fintype.card S) / beta α * hW M y x D + 2 / (beta α * N) := by sorry

end FocusSetRB
