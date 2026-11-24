-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PartialDerivativeAlgebra_pd_sub
-- name    : Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_sub
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:18:06.956282+00:00
-- url     : https://prove2.me/theorems/fe74ce47-5c45-49b9-8694-32f2a35840bc
-- title:
--   Partial Derivative Algebra: pd sub
-- statement:
--   The Partial Derivative Algebra construction uses the pd sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HomogeneityNaturalDegree.lean#L47-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HomogeneityNaturalDegree.lean#L47-L53

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

theorem Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra.pd_sub {a : ℕ} {P Q : Matrix (Fin N) (Fin N) ℂ → ℂ} (hP : U.IsPolyDeg a P) (hQ : U.IsPolyDeg a Q) :
    U.IsPolyDeg a (fun g => P g - Q g) := by sorry
