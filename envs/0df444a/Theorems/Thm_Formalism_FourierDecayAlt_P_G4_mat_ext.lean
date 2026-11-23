-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G4_mat_ext
-- name    : Formalism.FourierDecayAlt.P.G4.mat_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:39:36.106117+00:00
-- url     : https://prove2.me/theorems/cf9fd28a-2371-406b-a66f-a7271c2e3e7b
-- title:
--   G4: mat ext
-- statement:
--   The G4 construction uses the mat ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L48-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerBlockPoint.lean#L48-L62

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

theorem Formalism.FourierDecayAlt.P.G4.mat_ext {n : ℕ} {M N : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (h1 : ∀ i j : Fin n, M i.castSucc j.castSucc = N i.castSucc j.castSucc)
    (h2 : ∀ i : Fin n, M i.castSucc (Fin.last n) = N i.castSucc (Fin.last n))
    (h3 : ∀ j : Fin n, M (Fin.last n) j.castSucc = N (Fin.last n) j.castSucc)
    (h4 : M (Fin.last n) (Fin.last n) = N (Fin.last n) (Fin.last n)) : M = N := by sorry
