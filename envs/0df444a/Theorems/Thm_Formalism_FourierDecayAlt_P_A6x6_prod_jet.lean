-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_prod_jet
-- name    : Formalism.FourierDecayAlt.P.A6x6.prod_jet
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:39.362727+00:00
-- url     : https://prove2.me/theorems/5e6ffcfd-36fd-4dce-9c9a-2e5b128c9a4a
-- title:
--   A6x6: prod jet
-- statement:
--   The A6x6 construction uses the prod jet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussSumModulusOfLattice.lean#L71-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussSumModulusOfLattice.lean#L71-L87

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussSumModulusOfLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x6
open MvPolynomial
variable {m : ℕ}

theorem Formalism.FourierDecayAlt.P.A6x6.prod_jet (s : Finset (Fin m)) :
    (∏ k ∈ s, (1 + X k) - (1 + ∑ k ∈ s, X k + C (1 / 2 : ℚ) *
      ((∑ k ∈ s, X k) ^ 2 - ∑ k ∈ s, X k ^ 2)) : MvPolynomial (Fin m) ℚ) ∈
      idealOfVars (Fin m) ℚ ^ 3 := by sorry
