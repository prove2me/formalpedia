-- Prove2me | Theorems.Thm_APFB06_held_relation_pays_third_charge
-- name    : APFB06.held_relation_pays_third_charge
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:17:05.586292+00:00
-- url     : https://prove2.me/theorems/4b65b57e-f08d-4cf2-8de4-0df52f0f8768
-- title:
--   The proposed held-relation predicate yields a positive marginal charge
-- statement:
--   This theorem consumes the proposed predicate as a separate premise. It does not derive that predicate from the installed B06, bind its witness to an actual original alignment, or install the author-only B06 fidelity correction. Its conclusion is a marginal charge, not a premium over separately realized singleton prices. Assume B05 and the proposed HeldRelationExists predicate on the shared family-cost data. Then there exist a context, a nonempty finite family S and a task r outside S such that adding r raises cost by at least one floor and strictly raises cost. The existence predicate supplies testedness, both admissibilities and support novelty. Source: FOUNDATION_INPUTS revision 2026-10-04.1, B06; November 12 continuation and eight-decisions rulings, with each extra premise retained.
-- source:
--   Theorems/Thm_APFB06_held_relation_third_charge.lean, declaration at line 20 (Sib v15; source-scoped review). FOUNDATION_INPUTS revision 2026-10-04.1, B06; November 12 continuation and eight-decisions rulings, with each extra premise retained.

import Definitions.Def_APFB06_HeldRelation
import Theorems.Thm_APFB05_relation_strictly_dearer
import Theorems.Thm_APFB05_no_free_rider

set_option autoImplicit false
open APFPaper1.Source

theorem APFB06.held_relation_pays_third_charge
    {Context : Type*} {D P R Record : Context → Type*} [∀ g, DecidableEq (D g)]
    (wholeResource : (g : Context) → P g → R g)
    (calibration : (g : Context) → R g → NNReal)
    (maintained : (g : Context) → P g → Set (Record g))
    (sufficient : (g : Context) → P g → Set (Record g) → D g → Prop)
    (usesToRealize : (g : Context) → P g → D g → Set (Record g) → Prop)
    (tested : (g : Context) → D g → Prop)
    (C epsilon : Context → ℝ)
    (hB05 : APFB05.MarginalFloor wholeResource calibration maintained sufficient usesToRealize
      tested C epsilon)
    (hrel : APFB06.HeldRelationExists wholeResource calibration maintained sufficient usesToRealize
      tested C) :
    ∃ (g : Context) (S : Finset (D g)) (r : D g), S.Nonempty ∧ r ∉ S ∧
      familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) S + epsilon g ≤
        familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) (insert r S) ∧
      familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) S <
        familyCost (wholeResource g) (calibration g) (maintained g)
        (sufficient g) (usesToRealize g) (insert r S) := by sorry
