-- Prove2me | Theorems.Thm_Disjunctive_IntroDuality_regularity_condition_necessary
-- name    : Disjunctive.IntroDuality.regularity_condition_necessary
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T16:06:58.198988+00:00
-- url     : https://prove2.me/theorems/fec16747-894d-4810-be0b-973802913d00
-- title:
--   Corollary 1.6 — necessity of the Regularity Condition
-- statement:
--   This is Corollary 1.6 of Balas's *Disjunctive Programming*: the Regularity Condition of
--   Theorem 1.5 is not merely a convenient sufficient hypothesis, but genuinely necessary for the
--   clean dichotomy of that theorem to hold.
--
--   Using the notation of Theorem 1.5 — $(DP)$, $(DD)$, and the Regularity Condition on $Q^*,
--   Q^{**}$ — suppose the Regularity Condition **fails**, $(DP)$ is feasible, and $(DD)$ is
--   infeasible. Then $(DP)$ still has a **finite minimum**:
--
--   $$
--   \exists\, z_0 \in \mathbb{R} \text{ such that } z_0 = \min\{ c x : x \in \textstyle\bigcup_{h
--   \in Q} X_h \}.
--   $$
--
--   Under Theorem 1.5's dichotomy, an infeasible dual would normally force the primal to be either
--   infeasible or unbounded; this corollary exhibits the third possibility that opens up exactly
--   when the Regularity Condition is dropped — a finite-valued primal optimum with no matching
--   dual optimum, i.e. a genuine **duality gap**. This confirms that the Regularity Condition
--   cannot be weakened or removed from Theorem 1.5 without losing the strong-duality conclusion.
--
--   **Formalization Note.** The conclusion is stated as the existence of a finite optimal value
--   via `IsLeast`, matching "finite minimum" precisely (as opposed to `UnboundedBelowOn`, which
--   would be the negation of this in the presence of feasibility).
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 15, Corollary 1.6

import Mathlib
import Definitions.Def_Disjunctive_IntroDuality_PolyhedralSystems
import Definitions.Def_Disjunctive_IntroDuality_RegularityCondition

namespace Disjunctive.IntroDuality

/-- Corollary 1.6 (Balas §1.5, p. 15): the Regularity Condition of Theorem 1.5 is not just
sufficient but also necessary. If it fails, and `(DP)` is feasible while `(DD)` is infeasible,
then `(DP)` still has a finite minimum, i.e. there is a duality gap. -/
theorem regularity_condition_necessary {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ) (c : Fin n → ℝ)
    (hNotReg : ¬ RegularityCondition
                  (FeasibleIndices (fun h => PolyNonneg (A h) (b h)))
                  (FeasibleIndices (fun h => DualPoly (A h) c)))
    (hDP : (⋃ h : Q, PolyNonneg (A h) (b h)).Nonempty)
    (hDD : ¬ ∃ w : ℝ, ∃ u : (h : Q) → Fin (m h) → ℝ,
              ∀ h, u h ∈ DualPoly (A h) c ∧ w ≤ dotProduct (u h) (b h)) :
    ∃ v : ℝ, IsLeast ((fun x => dotProduct c x) '' (⋃ h : Q, PolyNonneg (A h) (b h))) v := by sorry

end Disjunctive.IntroDuality
