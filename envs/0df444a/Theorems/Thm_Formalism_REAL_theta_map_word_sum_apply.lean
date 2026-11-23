-- Prove2me | Theorems.Thm_Formalism_REAL_theta_map_word_sum_apply
-- name    : Formalism.REAL.theta_map_word_sum_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:45:41.618109+00:00
-- url     : https://prove2.me/theorems/943c2612-47f9-4af5-bef9-0b24f280b19f
-- title:
--   REAL: theta map word sum apply
-- statement:
--   The REAL construction uses the theta map word sum apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L209-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L209-L211

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}

theorem Formalism.REAL.theta_map_word_sum_apply {j : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (F : Arr V n j) :
    thetaA E j F = ∑ α : Fin j → Fin n × Fin n, ew E (List.ofFn α).reverse (F α) := by sorry
