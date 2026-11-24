-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PartialDerivativeAlgebra_pd_mono
-- name    : Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_mono
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:11:41.508787+00:00
-- url     : https://prove2.me/theorems/3fe9ebb5-1e32-464f-bc85-6b9bdac679f2
-- title:
--   Partial Derivative Algebra: pd mono
-- statement:
--   The Partial Derivative Algebra construction uses the pd mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HomogeneityNaturalDegree.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HomogeneityNaturalDegree.lean#L11-L14

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

theorem Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_mono {a b : ℕ} (hab : a ≤ b) {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg a P) :
    U.IsPolyDeg b P := by sorry
