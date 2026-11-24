-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_X_scaled_eq
-- name    : Formalism.FourierDecayAlt.P.X.scaled_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:04.53255+00:00
-- url     : https://prove2.me/theorems/b73b86be-d354-4c52-8c33-01b1b1fba726
-- title:
--   X: scaled eq
-- statement:
--   The X construction uses the scaled eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalingExponentIdentities.lean#L9-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ScalingExponentIdentities.lean#L9-L17

import Definitions.Def_Formalism_HermitianCurvature_StatementX
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalingExponentIdentities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix
open Formalism.FourierDecayAlt.P.X

theorem Formalism.FourierDecayAlt.P.X.scaled_eq {K : Type} [Field K] (n : ℕ) (Z : Matrix (Fin n) (Fin n) K) (κ : K) (l : ℕ)
    (hl : l ≤ n) :
    (Matrix.of (fun a b : Fin n => κ ^ ((a : ℕ) + (b : ℕ)) * Z a b)).submatrix
        (Fin.castLE hl) (Fin.castLE hl) =
      Matrix.diagonal (fun a : Fin l => κ ^ (a : ℕ)) * Z.submatrix (Fin.castLE hl) (Fin.castLE hl) *
        Matrix.diagonal (fun a : Fin l => κ ^ (a : ℕ)) := by sorry
