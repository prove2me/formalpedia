-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_comm_Tvprod
-- name    : Formalism.FourierDecayAlt.R.LevelData.inv_comm_Tvprod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:03:37.701278+00:00
-- url     : https://prove2.me/theorems/d9fd7074-3c2d-4a97-8fb0-f55d2608f65b
-- title:
--   Level Data: inv comm Tvprod
-- statement:
--   The Level Data construction uses the inv comm Tvprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleInv.lean#L74-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RuleInv.lean#L74-L81

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

theorem Formalism.FourierDecayAlt.R.LevelData.inv_comm_Tvprod {x : A} (hp : ∀ l, Commute x (L.pb l)) (hc : ∀ l, Commute x (L.cb l))
    (hci : ∀ l, Commute x (L.cbi l)) (Y : ℂ) (i j) : Commute x (L.Tvprod Y i j) := by sorry
