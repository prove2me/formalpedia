-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G4_blk_inj
-- name    : Formalism.FourierDecayAlt.P.G4.blk_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:25:53.674137+00:00
-- url     : https://prove2.me/theorems/71b89450-ebda-4cf5-899e-ce4329c4da24
-- title:
--   G4: blk inj
-- statement:
--   The G4 construction uses the blk inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L70-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L70-L86

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt.G
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G4

theorem Formalism.FourierDecayAlt.P.G4.blk_inj {n : ℕ} {A A' : Matrix (Fin n) (Fin n) ℂ} {b a b' a' : Fin n → ℂ} {e e' : ℂ} :
    blk A b a e = blk A' b' a' e' ↔ A = A' ∧ b = b' ∧ a = a' ∧ e = e' := by sorry
