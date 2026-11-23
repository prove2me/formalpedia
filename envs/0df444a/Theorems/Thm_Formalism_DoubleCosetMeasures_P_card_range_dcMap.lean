-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_card_range_dcMap
-- name    : Formalism.DoubleCosetMeasures.P.card_range_dcMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:26.784285+00:00
-- url     : https://prove2.me/theorems/a237a30c-34ed-4f79-b0ef-6f64d097d10b
-- title:
--   P: card range dc Map
-- statement:
--   The P construction uses the card range dc Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/DoubleCosetEqPreimage.lean#L154-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/DoubleCosetEqPreimage.lean#L154-L163

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

theorem Formalism.DoubleCosetMeasures.P.card_range_dcMap (K₀ : Subgroup G) (g : G) :
    Nat.card (Set.range (dcMap K₀ g)) = (K₀.map (MulAut.conj g).toMonoidHom).relIndex K₀ := by sorry
