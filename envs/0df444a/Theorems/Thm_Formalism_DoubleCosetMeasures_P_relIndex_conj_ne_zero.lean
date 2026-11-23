-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_relIndex_conj_ne_zero
-- name    : Formalism.DoubleCosetMeasures.P.relIndex_conj_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:55:53.982157+00:00
-- url     : https://prove2.me/theorems/2bd1a2f6-7c88-4aee-8739-107513dfa287
-- title:
--   P: rel Index conj ne zero
-- statement:
--   The P construction uses the rel Index conj ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/DoubleCosetEqPreimage.lean#L167-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/DoubleCosetEqPreimage.lean#L167-L181

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

theorem Formalism.DoubleCosetMeasures.P.relIndex_conj_ne_zero (K₀ : Subgroup G) (hK : IsOpen (K₀ : Set G))
    (hc : IsCompact (K₀ : Set G)) (g : G) :
    (K₀.map (MulAut.conj g).toMonoidHom).relIndex K₀ ≠ 0 := by sorry
