-- Prove2me | Theorems.Thm_Formalism_REAL_f1alg_comm_iff
-- name    : Formalism.REAL.f1alg_comm_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:08.630048+00:00
-- url     : https://prove2.me/theorems/c25347cc-ae5a-4f64-8516-241839c4cab7
-- title:
--   REAL: f1alg comm iff
-- statement:
--   The REAL construction uses the f1alg comm iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/MemUnitaryGroupIffMulConjTranspose.lean#L47-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/MemUnitaryGroupIffMulConjTranspose.lean#L47-L54

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.REAL

theorem Formalism.REAL.f1alg_comm_iff {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) :
    A * Jm ε = Jm ε * A ↔ Jm ε * A * Jm ε = A := by sorry
