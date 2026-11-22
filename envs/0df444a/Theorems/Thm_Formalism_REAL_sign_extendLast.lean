-- Prove2me | Theorems.Thm_Formalism_REAL_sign_extendLast
-- name    : Formalism.REAL.sign_extendLast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:57:53.672068+00:00
-- url     : https://prove2.me/theorems/3d23cdac-a34d-46cc-969b-ea699e3464a6
-- title:
--   REAL: sign extend Last
-- statement:
--   The REAL construction uses the sign extend Last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/GeneratorCommutatorQuantumDet.lean#L245-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/GeneratorCommutatorQuantumDet.lean#L245-L248

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL

theorem Formalism.REAL.sign_extendLast {m : ℕ} (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (extendLast τ) = Equiv.Perm.sign τ := by sorry
