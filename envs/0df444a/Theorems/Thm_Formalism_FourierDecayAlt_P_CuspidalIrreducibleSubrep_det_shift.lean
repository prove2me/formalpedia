-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CuspidalIrreducibleSubrep_det_shift
-- name    : Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep.det_shift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:57:43.010157+00:00
-- url     : https://prove2.me/theorems/cf099166-f78a-4477-a274-e0a7aaeb9b70
-- title:
--   Cuspidal Irreducible Subrep: det shift
-- statement:
--   The Cuspidal Irreducible Subrep construction uses the det shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CuspidalIrreducibleSubrep.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CuspidalIrreducibleSubrep.lean#L45-L51

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2 Formalism.FourierDecayAlt.P.G7

theorem Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep.det_shift {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsStrictUpper X) (t : ℂ) :
    (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X).det = t ^ n := by sorry
