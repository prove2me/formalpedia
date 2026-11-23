-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CuspidalIrreducibleSubrep_Mcoord_eq
-- name    : Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep.Mcoord_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:57:37.433974+00:00
-- url     : https://prove2.me/theorems/6cac6cb8-ca55-4cd8-9aa5-eaaa148c8dfb
-- title:
--   Cuspidal Irreducible Subrep: Mcoord eq
-- statement:
--   The Cuspidal Irreducible Subrep construction uses the Mcoord eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CuspidalIrreducibleSubrep.lean#L66-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CuspidalIrreducibleSubrep.lean#L66-L77

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

theorem Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep.Mcoord_eq {n : ℕ} (t : ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (B ρ : Fin n → ℂ) (σ : ℂ) :
    Mcoord t X B ρ σ = blk (wMat n) 0 0 1 * blk (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) B ρ σ := by sorry
