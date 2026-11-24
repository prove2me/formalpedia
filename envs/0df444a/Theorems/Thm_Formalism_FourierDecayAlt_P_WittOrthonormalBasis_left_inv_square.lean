-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WittOrthonormalBasis_left_inv_square
-- name    : Formalism.FourierDecayAlt.P.WittOrthonormalBasis.left_inv_square
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:01:50.451724+00:00
-- url     : https://prove2.me/theorems/92896d5a-bf16-4475-8250-6ff140e56000
-- title:
--   Witt Orthonormal Basis: left inv square
-- statement:
--   The Witt Orthonormal Basis construction uses the left inv square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WittOrthonormalBasis.lean#L20-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WittOrthonormalBasis.lean#L20-L22

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagGramRestriction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WittOrthonormalBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.WittOrthonormalBasis
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector FlagGramRestriction
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.WittOrthonormalBasis.left_inv_square {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ] (W : Matrix (Fin n) κ ℂ)
    (L : Matrix κ (Fin n) ℂ) (hcard : Fintype.card κ = n) (h : L * W = 1) : W * L = 1 := by sorry
