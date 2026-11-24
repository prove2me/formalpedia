-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PartialDerivativeAlgebra_pd_det
-- name    : Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_det
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T15:20:59.988564+00:00
-- url     : https://prove2.me/theorems/882ef95e-a7ce-494d-b9a2-db9d1965686d
-- title:
--   Partial Derivative Algebra: pd det
-- statement:
--   The Partial Derivative Algebra construction uses the pd det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HomogeneityNaturalDegree.lean#L78-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HomogeneityNaturalDegree.lean#L78-L88

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MvPolynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra
variable {N : ℕ}

theorem Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_det {l : ℕ} (M : Matrix (Fin N) (Fin N) ℂ → Matrix (Fin l) (Fin l) ℂ)
    (h : ∀ a b, U.IsPolyDeg 1 (fun g => M g a b)) : U.IsPolyDeg l (fun g => (M g).det) := by sorry
