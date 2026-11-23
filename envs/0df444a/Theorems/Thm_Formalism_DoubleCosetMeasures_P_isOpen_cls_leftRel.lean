-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_isOpen_cls_leftRel
-- name    : Formalism.DoubleCosetMeasures.P.isOpen_cls_leftRel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:44.217077+00:00
-- url     : https://prove2.me/theorems/1291b812-dc7f-407b-80b8-de33a291e5c8
-- title:
--   P: is Open cls left Rel
-- statement:
--   The P construction uses the is Open cls left Rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/DoubleCosetEqPreimage.lean#L183-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/DoubleCosetEqPreimage.lean#L183-L185

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
variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem Formalism.DoubleCosetMeasures.P.isOpen_cls_leftRel (K₀ : Subgroup G) (hK : IsOpen (K₀ : Set G)) (q : G ⧸ K₀) :
    IsOpen (cls (QuotientGroup.leftRel K₀) q) := by sorry
