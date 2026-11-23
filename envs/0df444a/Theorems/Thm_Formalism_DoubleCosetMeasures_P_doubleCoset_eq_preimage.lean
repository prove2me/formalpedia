-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_doubleCoset_eq_preimage
-- name    : Formalism.DoubleCosetMeasures.P.doubleCoset_eq_preimage
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:15.466804+00:00
-- url     : https://prove2.me/theorems/0b490b9a-f992-493a-baf9-e223f30db2dc
-- title:
--   P: double Coset eq preimage
-- statement:
--   The P construction uses the double Coset eq preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/DoubleCosetEqPreimage.lean#L132-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/DoubleCosetEqPreimage.lean#L132-L145

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

theorem Formalism.DoubleCosetMeasures.P.doubleCoset_eq_preimage (K₀ : Subgroup G) (g : G) :
    DoubleCoset.doubleCoset g (K₀ : Set G) K₀ =
      (QuotientGroup.mk : G → G ⧸ K₀) ⁻¹' Set.range (dcMap K₀ g) := by sorry
