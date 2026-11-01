-- Prove2me | Theorems.Thm_FocusSetRB_lemma_4
-- name    : FocusSetRB.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:21:34.640597+00:00
-- url     : https://prove2.me/theorems/a12ef353-b473-4c4d-a167-b3889e4050f9
-- title:
--   Lemma 4, eq. (37), p.18 — the set-expansion policy satisfies Condition 2
-- statement:
--   Let $y^*$ be an optimal solution of (LP) whose policy $\bar\pi^*$ induces an aperiodic unichain (Assumption 1), let $0<\alpha<1$, $\beta=\min\{\alpha,1-\alpha\}$, $N\ge1$ and $k=\alpha N\in\mathbb N$. Consider a focus-set update obeying Algorithm 2, lines 2–5, and a rectifier obeying Algorithm 1's (4)–(5). For every system state $x$, every previous focus set $D_{\mathrm{prev}}$ and every focus set $D$ the update can choose from $(x,D_{\mathrm{prev}})$: draw the ideal actions, the rectified actions $A$, the next state $X'$ and the next focus set $D''$ from the update at $(X',D)$. Then
--
--   $$
--   \mathbb E\big[(m(D)-m(D''))^+\big]\le\frac{|\mathbb S|^{1/2}+1}{\beta\sqrt N}+\frac{1+(\beta+1)|\mathbb S|}{\beta N}.
--   $$
--
--   In the paper's words, $\mathbb E[(m(D_t)-m(D_{t+1}))^+\mid X_t,D_t]$ obeys this bound almost surely: the focus set does not shrink much in expectation (Condition 2, almost non-shrinking).
--
--   Differences from the source:
--   - generalization: the set-expansion policy of Algorithm 2 ("any set with the largest m(D_t)", uniform tie-breaking in lines 6–15) → every update kernel whose possible outputs obey lines 2–5 and every rectifier kernel whose possible outputs obey Algorithm 1's (4)–(5); reason: contains Algorithm 2 with every choice of maximizer and its uniform tie-breaking; p.10 says the analysis holds whenever lines 4–5 of Algorithm 1 are satisfied
--   - generalization: a.s., for the time-t pair (X_t, D_t) of the policy started at D_{−1} = ∅ → for every state x, every previous focus set D_prev and every D the update can choose from (x, D_prev); reason: every pair (X_t, D_t) of positive probability is of this form, so the pointwise bound implies the a.s. bound
--   - encoding: μ* is the stationary distribution of P_π̄* → μ*(s) := y*(s,0) + y*(s,1); reason: the paper states this identity on p.7; it is stationary by (2b) and (3) and is the unique stationary law under Assumption 1, so the same vector
--   - encoding: αN an integer, N arms → k : ℕ with (k : ℝ) = α·N and N ≥ 1; reason: the paper assumes αN is an integer (p.5); an N-armed problem has N ≥ 1
--   - encoding: P_π̄* induces an aperiodic unichain (a single recurrent class and a possibly empty set of transient states) → some state is recurrent, any two recurrent states reach each other, and every recurrent state has period 1; transient states are unconstrained; reason: the same property of a finite chain spelled out state by state; the period of a state is the gcd of its return times
--   - reading: D_t chosen based on X_t and D_{t−1}, actions based on X_t and D_t (Algorithm 1), "any set" in Algorithm 2 → the update and the rectifier are fixed kernels that do not depend on t; reason: Algorithm 1 names those as the inputs of the rule, and Appendix D (p.40) treats (S_t, A_t, X_t, D_t) as a finite-state Markov chain
--   - encoding: arms indexed by [N] = {1,…,N} → arms indexed by Fin N = {0,…,N−1}; reason: relabelling only
-- source:
--   Hong, Xie, Chen, Wang, Unichain and Aperiodicity are Sufficient for Asymptotic Optimality of Average-Reward Restless Bandits, arXiv:2402.05689v4, Lemma 4, eq. (37), p.18

import Mathlib
import Definitions.Def_FocusSetRB_LPFeasible
import Definitions.Def_FocusSetRB_IsAperiodicUnichain
import Definitions.Def_FocusSetRB_IsSetExpansionSelector

namespace FocusSetRB

/-- **Lemma 4 (Set-expansion policy satisfies Condition 2), eq. (37), p.18** (Hong, Xie, Chen, Wang, arXiv:2402.05689v4).
Consider the set-expansion policy in Algorithm 2. For any `t ≥ 0`,
`𝔼[(m(D_t) − m(D_{t+1}))⁺ | X_t, D_t] ≤ (|𝕊|^{1/2} + 1)/(β√N) + (1 + (β + 1)|𝕊|)/(βN)` a.s.,
with `β = min{α, 1 − α}`.

Here `y` is an optimal solution of (LP) whose policy `π̄*` (3) induces an aperiodic unichain
(Assumption 1, p.7, the paper's standing assumption).

**Formalization Note.** The set-expansion policy is any focus-set process whose update kernel
obeys Algorithm 2, lines 2–5 (`IsSetExpansionSelector`), and whose rectifier obeys Algorithm 1's
(4)–(5) (`IsRectifier`); Algorithm 2's lines 6–15 are one such rectifier (p.10). "a.s. given
`X_t, D_t`" is proved at **every** state `x`, every previous focus set `Dprev` and every `D` the
update can choose from `(x, Dprev)`, whatever the time step. Arms are `Fin N`, `N ≥ 1`,
`k = αN`. The expectation is over the ideal actions `Â_t`, the rectified actions `A_t`, the next
state `X_{t+1}` and the next focus set `D_{t+1} ∼ sel(X_{t+1}, D_t)`; `(a)⁺ = max a 0`. -/
theorem lemma_4 {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (M : SingleArmMDP S) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {y : S → Bool → ℝ} (hy : IsLPOptimal M α y) (hU : IsAperiodicUnichain (Ppi M y))
    {N k : ℕ} (hN : 1 ≤ N) (hk : (k : ℝ) = α * N)
    (sel : (Fin N → S) → Finset (Fin N) → Finset (Fin N) → ℝ)
    (hsel : IsSetExpansionSelector α y sel)
    (rect : (Fin N → S) → Finset (Fin N) → (Fin N → Bool) → (Fin N → Bool) → ℝ)
    (hrect : IsRectifier k rect)
    (x : Fin N → S) (Dprev D : Finset (Fin N)) (hD : 0 < sel x Dprev D) :
    ∑ Ahat, idealLaw y x Ahat * ∑ A, rect x D Ahat A *
        ∑ x', stepProb M x A x' * ∑ D', sel x' D D' * max (frac D - frac D') 0 ≤
      (Real.sqrt (Fintype.card S) + 1) / (beta α * Real.sqrt N) +
        (1 + (beta α + 1) * Fintype.card S) / (beta α * N) := by sorry

end FocusSetRB
