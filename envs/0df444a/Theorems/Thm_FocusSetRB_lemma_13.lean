-- Prove2me | Theorems.Thm_FocusSetRB_lemma_13
-- name    : FocusSetRB.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:18:50.955761+00:00
-- url     : https://prove2.me/theorems/a6095ee4-259f-4b19-8590-09dbc75996d3
-- title:
--   Lemma 13, eq. (115), p.48 — one-step growth of the $L_1$ distance on $D$
-- statement:
--   Let $y^*$ be an optimal solution of (LP) whose policy $\bar\pi^*$ induces an aperiodic unichain (Assumption 1) and let $N\ge1$. For every system state $x$ and every $D\subseteq[N]$, if the arms of $D$ take actions $A_0(i)\sim\bar\pi^*(\cdot\mid x(i))$ and the other arms take any actions,
--
--   $$
--   \mathbb E\Big[\big(\|X_1(D)-m(D)\mu^*\|_1-\|x(D)-m(D)\mu^*\|_1\big)^+\ \Big|\ X_0=x\Big]\le\frac{2|\mathbb S|^{1/2}}{\sqrt N},
--   $$
--
--   where $a^+=\max\{a,0\}$.
--
--   This controls how much the slack $\delta(X_{t+1},D_t)$ can fall below $\delta(X_t,D_t)$, which is the main input of Lemma 4.
--
--   Differences from the source:
--   - encoding: A₀(i) ∼ π̄*(·|S₀(i)) for i ∈ D, the actions of the other arms unspecified → the other arms take arbitrary actions aOut, quantified over every choice; reason: the quantity depends only on the arms of D, whose next states depend only on their own actions, so every law of the other actions gives the same expectation
--   - encoding: μ* is the stationary distribution of P_π̄* → μ*(s) := y*(s,0) + y*(s,1); reason: the paper states this identity on p.7; it is stationary by (2b) and (3) and is the unique stationary law under Assumption 1, so the same vector
--   - encoding: arms indexed by [N] = {1,…,N} → arms indexed by Fin N = {0,…,N−1}; reason: relabelling only
--   - encoding: P_π̄* induces an aperiodic unichain (a single recurrent class and a possibly empty set of transient states) → some state is recurrent, any two recurrent states reach each other, and every recurrent state has period 1; transient states are unconstrained; reason: the same property of a finite chain spelled out state by state; the period of a state is the gcd of its return times
-- source:
--   Hong, Xie, Chen, Wang, Unichain and Aperiodicity are Sufficient for Asymptotic Optimality of Average-Reward Restless Bandits, arXiv:2402.05689v4, Lemma 13, eq. (115), p.48

import Mathlib
import Definitions.Def_FocusSetRB_LPFeasible
import Definitions.Def_FocusSetRB_IsAperiodicUnichain
import Definitions.Def_FocusSetRB_scaledCount

namespace FocusSetRB

/-- **Lemma 13, eq. (115), p.48** (Hong, Xie, Chen, Wang, arXiv:2402.05689v4). For any system state `x` and any subset
`D ⊆ [N]`,
`𝔼[(‖X₁(D) − m(D)μ*‖₁ − ‖x(D) − m(D)μ*‖₁)⁺ | X₀ = x, A₀(i) ∼ π̄*(·|S₀(i)) ∀ i ∈ D] ≤
2|𝕊|^{1/2}/√N`.

Here `y` is an optimal solution of (LP) whose policy `π̄*` (3) induces an aperiodic unichain
(Assumption 1, p.7, the paper's standing assumption).

**Formalization Note.** Arms are `Fin N`, `N ≥ 1`; `(a)⁺ = max a 0`. The arms of `D` take their
ideal actions and the arms outside `D` take arbitrary actions `aOut` (quantified universally);
the expectation is over the ideal actions and the next state. -/
theorem lemma_13 {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (M : SingleArmMDP S) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {y : S → Bool → ℝ} (hy : IsLPOptimal M α y) (hU : IsAperiodicUnichain (Ppi M y))
    {N : ℕ} (hN : 1 ≤ N) (x : Fin N → S) (D : Finset (Fin N)) (aOut : Fin N → Bool) :
    ∑ Ahat, idealLaw y x Ahat *
        ∑ x', stepProb M x (followOn D Ahat aOut) x' * max (l1Dev y x' D - l1Dev y x D) 0 ≤
      2 * Real.sqrt (Fintype.card S) / Real.sqrt N := by sorry

end FocusSetRB
