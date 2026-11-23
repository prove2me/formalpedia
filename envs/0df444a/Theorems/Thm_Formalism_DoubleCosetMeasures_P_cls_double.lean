-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_cls_double
-- name    : Formalism.DoubleCosetMeasures.P.cls_double
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:34.474284+00:00
-- url     : https://prove2.me/theorems/a3669ebc-7de6-4007-9547-cb2d8d0bb1af
-- title:
--   P: cls double
-- statement:
--   The P construction uses the cls double property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/DoubleCosetEqPreimage.lean#L217-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/DoubleCosetEqPreimage.lean#L217-L223

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

theorem Formalism.DoubleCosetMeasures.P.cls_double {G : Type} [Group G] (K₀ : Subgroup G)
    (q : Quotient (DoubleCoset.setoid (K₀ : Set G) (K₀ : Set G))) :
    cls (DoubleCoset.setoid (K₀ : Set G) (K₀ : Set G)) q =
      DoubleCoset.doubleCoset (Quotient.out q) (K₀ : Set G) K₀ := by sorry
