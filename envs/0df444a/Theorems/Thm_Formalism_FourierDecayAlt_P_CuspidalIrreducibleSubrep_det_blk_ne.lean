-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CuspidalIrreducibleSubrep_det_blk_ne
-- name    : Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep.det_blk_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:58:13.647832+00:00
-- url     : https://prove2.me/theorems/c0c70f2f-197c-4be3-a5a9-80402d28d868
-- title:
--   Cuspidal Irreducible Subrep: det blk ne
-- statement:
--   The Cuspidal Irreducible Subrep construction uses the det blk ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CuspidalIrreducibleSubrep.lean#L79-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CuspidalIrreducibleSubrep.lean#L79-L101

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

theorem Formalism.FourierDecayAlt.P.CuspidalIrreducibleSubrep.det_blk_ne {n : ℕ} (t : ℂ) (ht : t ≠ 0) (X : Matrix (Fin n) (Fin n) ℂ) (hX : IsStrictUpper X)
    (B ρ : Fin n → ℂ) (σ : ℂ) :
    (blk (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) B ρ σ).det = t ^ n * σ - ρ ⬝ᵥ (geoS X t *ᵥ B) := by sorry
