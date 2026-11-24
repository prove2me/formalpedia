-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_XGen_scaled_eq
-- name    : Formalism.FourierDecayAlt.P.XGen.scaled_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:02.397816+00:00
-- url     : https://prove2.me/theorems/40370394-c65e-4d9c-8a94-c58967a79ec4
-- title:
--   XGen: scaled eq
-- statement:
--   The XGen construction uses the scaled eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinorScalingLawGeneral.lean#L9-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinorScalingLawGeneral.lean#L9-L18

import Definitions.Def_Formalism_HermitianCurvature_StatementX
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinorScalingLawGeneral
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
open Formalism.FourierDecayAlt.P.XGen

theorem Formalism.FourierDecayAlt.P.XGen.scaled_eq {K : Type} [Field K] (n : ℕ) (Z : Matrix (Fin n) (Fin n) K) (α β : Fin n → K)
    (l : ℕ) (hl : l ≤ n) :
    (Matrix.of (fun a b : Fin n => α a * β b * Z a b)).submatrix
        (Fin.castLE hl) (Fin.castLE hl) =
      Matrix.diagonal (fun a : Fin l => α (Fin.castLE hl a)) *
          Z.submatrix (Fin.castLE hl) (Fin.castLE hl) *
        Matrix.diagonal (fun a : Fin l => β (Fin.castLE hl a)) := by sorry
