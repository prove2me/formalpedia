-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_hR_bar
-- name    : Formalism.FourierDecayAlt.R.LevelData.inv_hR_bar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:35.946527+00:00
-- url     : https://prove2.me/theorems/49bc4d1d-fa70-4975-86a6-7d4a4fd6c086
-- title:
--   Level Data: inv h R bar
-- statement:
--   The Level Data construction uses the inv h R bar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleInv.lean#L103-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleInv.lean#L103-L120

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.PInv
open Matrix LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]
variable {r : ℕ} (L : LevelData A r)

theorem Formalism.FourierDecayAlt.R.LevelData.inv_hR_bar (Y : ℂ) :
    L.G * L.Dbi * L.Dbi * L.Ahatv Y = L.Dr * L.GG * (L.ζbi * L.ζbi * L.Avr Y) := by sorry
