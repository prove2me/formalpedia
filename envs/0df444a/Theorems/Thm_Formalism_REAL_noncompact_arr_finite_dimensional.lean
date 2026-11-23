-- Prove2me | Theorems.Thm_Formalism_REAL_noncompact_arr_finite_dimensional
-- name    : Formalism.REAL.noncompact_arr_finite_dimensional
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:45:22.180919+00:00
-- url     : https://prove2.me/theorems/6f4a248c-8694-4450-89e3-5e961ef29b4f
-- title:
--   REAL: noncompact arr finite dimensional
-- statement:
--   The REAL construction uses the noncompact arr finite dimensional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L256-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L256-L279

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

theorem Formalism.REAL.noncompact_arr_finite_dimensional {j : ℕ} {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {u : V}
    (hfd : FiniteDimensional ℂ (kSpan ε E u)) : FiniteDimensional ℂ (arrV0 ε E u j) := by sorry
