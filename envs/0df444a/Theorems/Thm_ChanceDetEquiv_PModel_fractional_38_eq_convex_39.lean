-- Prove2me | Theorems.Thm_ChanceDetEquiv_PModel_fractional_38_eq_convex_39
-- name    : ChanceDetEquiv.PModel.fractional_38_eq_convex_39
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:58:14.547228+00:00
-- url     : https://prove2.me/theorems/025f4544-14c3-43e2-9bf9-ee9b27b9ab8f
-- title:
--   Programs (38) and (39) — equal suprema with a convex transformed program
-- statement:
--   For positive row and decision dimensions, let the corrected fractional P-model program (38) have at least one feasible point. For the same probability model, moments, and confidence levels, the full feasible set of (39), including $t=0$, is convex. Every feasible point of (38) maps by (39a) to a feasible point of (39) with the same objective value. Moreover,
--   $$
--   \sup_{(D,v,v_0,w_0)\in F_{38}}\frac{v_0}{w_0}
--   =\sup_{(\bar D,\bar v,\bar v_0,\bar w_0,t)\in F_{39}}\bar v_0.
--   $$
--   Thus the one convex program (39) has the same optimal value, finite or infinite, as (38). An optimizer of (39) with $t>0$ has an inverse point in (38), but the equality of suprema also covers all $t=0$ points.
--
--   **Formalization Note** The paper's phrase “replace ... by one convex programming problem” is read as convexity, a value-preserving forward substitution, and equality of extended-real suprema. Nonemptiness of (38) is stated because (39) can contain boundary points even when (38) has none. The standing Gaussian row-law assumption is included. The printed square-and-sign error in (38) is corrected using (29) and (39); $w_0>0$ and $t\ge0$ retain the stated domains.
-- source:
--   Charnes and Cooper, Deterministic Equivalents for Optimizing and Satisficing under Chance Constraints, Oper. Res. 11 (1963), pp. 32–33, Eqs. (38)–(39b), p. 32 paragraph preceding (39), and p. 33 paragraph after (39b); https://doi.org/10.1287/opre.11.1.18

import Definitions.Def_ChanceDetEquiv_PModel_Model

namespace ChanceDetEquiv.PModel

open MeasureTheory

/-- Programs (38) and (39) have the same extended-real supremum; the full transformed feasible set includes t = 0. -/
theorem fractional_38_eq_convex_39 {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (d : Model Ω m n) [IsProbabilityMeasure d.P]
    (hm : 0 < m) (hn : 0 < n)
    (hMoments : MomentAssumptions d) (hNormal : NormalRows d)
    (hConfidence : Confidence d)
    (hNonempty : (feasible38 d).Nonempty) :
    Convex ℝ (feasible39 d) ∧
      (∀ p : Point38 m n, p ∈ feasible38 d →
        forward p ∈ feasible39 d ∧ value39 (forward p) = value38 p) ∧
      sSup (values38 d) = sSup (values39 d) := by sorry

end ChanceDetEquiv.PModel
