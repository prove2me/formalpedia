-- Prove2me | Theorems.Thm_Formalism_REAL_rho_rhoN_bound
-- name    : Formalism.REAL.rho_rhoN_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:45:39.669564+00:00
-- url     : https://prove2.me/theorems/e4efe021-dad1-4812-9b43-77afc101a7bb
-- title:
--   REAL: rho rho N bound
-- statement:
--   The REAL construction uses the rho rho N bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/HalfSumRootsStandard.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/HalfSumRootsStandard.lean#L14-L21

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HalfSumRootsStandard
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

theorem Formalism.REAL.rho_rhoN_bound {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    -((n : ℝ) / 2) ≤ rhoN ε a ∧ rhoN ε a ≤ (n : ℝ) / 2 := by sorry
