-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_X_mem
-- name    : Formalism.FourierDecayAlt.P.A6x6.X_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:06:36.357799+00:00
-- url     : https://prove2.me/theorems/f0669bcb-b50c-4a7e-b500-00adff075781
-- title:
--   A6x6: X mem
-- statement:
--   The A6x6 construction uses the X mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussSumModulusOfLattice.lean#L56-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussSumModulusOfLattice.lean#L56-L57

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

theorem Formalism.FourierDecayAlt.P.A6x6.X_mem (k : Fin m) : (X k : MvPolynomial (Fin m) ℚ) ∈ idealOfVars (Fin m) ℚ := by sorry
