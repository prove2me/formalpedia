-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CuspidalIrreducibleSubrep_continuous_blk_shift
-- name    : Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep.continuous_blk_shift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:58:03.355068+00:00
-- url     : https://prove2.me/theorems/6538529a-1566-47d9-80fb-a9da0ae055fd
-- title:
--   Cuspidal Irreducible Subrep: continuous blk shift
-- statement:
--   The Cuspidal Irreducible Subrep construction uses the continuous blk shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CuspidalIrreducibleSubrep.lean#L103-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CuspidalIrreducibleSubrep.lean#L103-L106

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

theorem Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep.continuous_blk_shift {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) :
    Continuous fun t : ℂ => blk (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) B ρ σ := by sorry
