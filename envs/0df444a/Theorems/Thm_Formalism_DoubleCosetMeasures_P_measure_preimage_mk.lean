-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_measure_preimage_mk
-- name    : Formalism.DoubleCosetMeasures.P.measure_preimage_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:47.405156+00:00
-- url     : https://prove2.me/theorems/e3c29626-f4f7-4fc7-9bf2-f13438609c68
-- title:
--   P: measure preimage mk
-- statement:
--   The P construction uses the measure preimage mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/DoubleCosetEqPreimage.lean#L189-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/DoubleCosetEqPreimage.lean#L189-L203

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
variable [MeasurableSpace G] [BorelSpace G]

theorem Formalism.DoubleCosetMeasures.P.measure_preimage_mk (μ : Measure G) [μ.IsMulLeftInvariant] (K₀ : Subgroup G)
    (hK : IsOpen (K₀ : Set G)) (S : Set (G ⧸ K₀)) (hS : S.Finite) :
    μ ((QuotientGroup.mk : G → G ⧸ K₀) ⁻¹' S) = (Nat.card S : ENNReal) * μ (K₀ : Set G) := by sorry
