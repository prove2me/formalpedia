-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_mem_mulR_iff
-- name    : Formalism.FourierDecayAlt.P.A6x4.mem_mulR_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:38:49.381442+00:00
-- url     : https://prove2.me/theorems/0a59ad93-32bb-47be-858d-b36da4c3a7ba
-- title:
--   A6x4: mem mul R iff
-- statement:
--   The A6x4 construction uses the mem mul R iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModulusLocallyConstant.lean#L74-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModulusLocallyConstant.lean#L74-L88

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x4
variable {K : Type} [CommRing K]

theorem Formalism.FourierDecayAlt.P.A6x4.mem_mulR_iff {R : Subring K} {a b : K} (hab : a * b = 1) (x : K) :
    x ∈ mulR R a ↔ b * x ∈ R := by sorry
