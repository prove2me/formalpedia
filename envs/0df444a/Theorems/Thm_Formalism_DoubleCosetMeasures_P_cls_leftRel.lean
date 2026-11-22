-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_cls_leftRel
-- name    : Formalism.DoubleCosetMeasures.P.cls_leftRel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:30.372805+00:00
-- url     : https://prove2.me/theorems/c911b947-bcb3-4d4a-ab1f-fb44c93ab751
-- title:
--   P: cls left Rel
-- statement:
--   The P construction uses the cls left Rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/DoubleCosetEqPreimage.lean#L88-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/DoubleCosetEqPreimage.lean#L88-L101

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_DoubleCosetEqPreimage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
variable {G : Type} [Group G]

theorem Formalism.DoubleCosetMeasures.P.cls_leftRel (K₀ : Subgroup G) (q : G ⧸ K₀) :
    cls (QuotientGroup.leftRel K₀) q = (fun z => q.out⁻¹ * z) ⁻¹' (K₀ : Set G) := by sorry
