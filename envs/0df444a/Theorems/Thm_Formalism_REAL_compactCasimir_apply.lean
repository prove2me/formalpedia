-- Prove2me | Theorems.Thm_Formalism_REAL_compactCasimir_apply
-- name    : Formalism.REAL.compactCasimir_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:08.568045+00:00
-- url     : https://prove2.me/theorems/d506355a-6df0-4dca-be73-eccdd3a79d11
-- title:
--   REAL: compact Casimir apply
-- statement:
--   The REAL construction uses the compact Casimir apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L131-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/FirstSlotSliceSlotMixedCasimirZero.lean#L131-L138

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
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
variable {W : Type*} [AddCommGroup W] [Module ℂ W] {n : ℕ}

theorem Formalism.REAL.compactCasimir_apply (ε : Fin n → Bool) (T : Fin n → Fin n → Module.End ℂ W) (x : W) :
    CasK ε T x = ∑ a, ∑ b, if ε a = ε b then T a b (T b a x) else 0 := by sorry
