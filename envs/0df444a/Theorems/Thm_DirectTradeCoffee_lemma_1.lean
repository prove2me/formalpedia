-- Prove2me | Theorems.Thm_DirectTradeCoffee_lemma_1
-- name    : DirectTradeCoffee.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:51:20.798023+00:00
-- url     : https://prove2.me/theorems/af8a82cf-4f90-42e3-90f2-24677ead4cda
-- title:
--   Lemma 1, p.12 — $\Pr(q^*<Q\tilde y)=0$ iff $Q\le Q_L$, $=1$ iff $Q>Q_H$ or $Q=Q_H$ without an atom (corrected: atom at $(\varphi_l,y_l)$)
-- statement:
--   Let $Q\ge0$ and let $q^*(Q,\varphi,y)$ be the second-stage optimal quantity. Then
--
--   1. $\Pr\big(q^*(Q,\tilde\varphi,\tilde y) < Q\tilde y\big) = 0$ if and only if $Q\le Q_L$;
--   2. $\Pr\big(q^*(Q,\tilde\varphi,\tilde y) < Q\tilde y\big) = 1$ if and only if $Q>Q_H$, or $Q=Q_H$ and $F(\{(\varphi_l,y_l)\})=0$.
--
--   Thus up to $Q_L$ no bean is ever downgraded to the blend label, and beyond $Q_H$ some beans always are. This is the meaning of the specialized and diversified classes.
--
--   **Formalization Note** The event is written "every optimal second-stage quantity is below $Qy$", which avoids choosing a maximizer; by Proposition 1 there is exactly one on the support.
--
--   Differences from the source:
--   - correction: Pr(q* < Qỹ) = 1 iff Q ≥ Q_H → Pr(q* < Qỹ) = 1 iff Q > Q_H, or Q = Q_H and F{(φ_l, y_l)} = 0; reason: at Q = Q_H the supply binds at the corner (φ_l, y_l); counterexample: F = ½ Unif([13, 17] × [0.5, 2.5]) + ½ δ_(13, 0.5) has support Ω and E[ỹ] = 1 but Pr(q* < Q_H ỹ) = ½
--   - encoding: the event q*(Q, φ̃, ỹ) < Qỹ → every optimal second-stage quantity is < Qy; reason: Proposition 1 gives a unique optimal quantity on Ω, so the two events agree up to an F-null set
--   - generalization: v > v_B (p.9; p.31 prints v_B > v) → no order between v and v_B is assumed; reason: no step uses it, and p.9 and p.31 disagree; every instance of the paper is covered
--   - reading: p.13 illustrates a capacity limit Q_max by k′(Q_max) = ∞ → k is real-valued and continuous on [0, ∞), as p.10 and p.31 assume; reason: the illustration lies outside the model assumption that k is a continuous function; every k of the model is covered
--   - encoding: second-stage constraint 0 ≤ q ≤ 1 → 0 ≤ q < 1; reason: at q = 1 no finite price clears the market and the objective tends to −∞; the maximum and its maximizer are unchanged
--   - encoding: F has support Ω → F(Ωᶜ) = 0 and every open ball around a point of Ω has positive mass; reason: this is the definition of the support of a measure
-- source:
--   Webster–Kazaz–Gheibi, Direct Trade Sourcing Strategies for Specialty Coffee, MSOM (2024), doi:10.1287/msom.2021.0586, Lemma 1, p.12; proof pp.40–41

import Mathlib
import Definitions.Def_DirectTradeCoffee_Model

namespace DirectTradeCoffee

/-- **Lemma 1** (corrected), Webster–Kazaz–Gheibi, *Direct Trade Sourcing Strategies for Specialty
Coffee*, MSOM (2024), doi:10.1287/msom.2021.0586, p.12: when downward substitution happens.

For `Q ≥ 0`, `Pr(q* < Qỹ) = 0` iff `Q ≤ Q_L`, and `Pr(q* < Qỹ) = 1` iff `Q > Q_H`, or `Q = Q_H` and
the corner `(φ_l, y_l)` is not an atom of `F`.

**Formalization Note.** The event `q*(Q, φ̃, ỹ) < Qỹ` is written "every optimal second-stage quantity
is `< Qy`", which avoids choosing a maximizer: Proposition 1 gives exactly one on the support. The
printed second equivalence reads "iff `Q ≥ Q_H`"; it fails when `F` has an atom at `(φ_l, y_l)`,
where `Q_H y_l = q°(φ_l)`. -/
theorem lemma_1 (P : Params) {k : ℝ → ℝ} (hk : IsCost k) (U : Uncertainty) (Q : ℝ) (hQ : 0 ≤ Q) :
    (U.F {z : ℝ × ℝ | ∀ q, IsOptimalQuantity P k Q z.1 z.2 q → q < Q * z.2} = 0 ↔ Q ≤ QL P U) ∧
    (U.F {z : ℝ × ℝ | ∀ q, IsOptimalQuantity P k Q z.1 z.2 q → q < Q * z.2} = 1 ↔
      QH P U < Q ∨ (Q = QH P U ∧ U.F {(U.φl, U.yl)} = 0)) := by sorry

end DirectTradeCoffee
