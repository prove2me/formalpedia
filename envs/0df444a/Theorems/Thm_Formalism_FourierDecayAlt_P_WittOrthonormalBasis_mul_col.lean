-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WittOrthonormalBasis_mul_col
-- name    : Formalism.FourierDecayAlt.P.WittOrthonormalBasis.mul_col
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:02:15.704081+00:00
-- url     : https://prove2.me/theorems/3ced54dd-6a6c-4fcc-a6ce-7c3731779982
-- title:
--   Witt Orthonormal Basis: mul col
-- statement:
--   The Witt Orthonormal Basis construction uses the mul col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WittOrthonormalBasis.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WittOrthonormalBasis.lean#L16-L18

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

theorem Formalism.FourierDecayAlt.P.WittOrthonormalBasis.mul_col {m κ μ : Type*} [Fintype κ] (M : Matrix m κ ℂ) (N : Matrix κ μ ℂ) (i : m) (j : μ) :
    (M * N) i j = (M *ᵥ fun a => N a j) i := by sorry
