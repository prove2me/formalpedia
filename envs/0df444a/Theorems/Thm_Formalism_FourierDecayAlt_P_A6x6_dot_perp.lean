-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x6_dot_perp
-- name    : Formalism.FourierDecayAlt.P.A6x6.dot_perp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:50.724728+00:00
-- url     : https://prove2.me/theorems/7e0108b7-6436-43be-ada4-d606c3c7fef0
-- title:
--   A6x6: dot perp
-- statement:
--   The A6x6 construction uses the dot perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussSumModulusOfLattice.lean#L218-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussSumModulusOfLattice.lean#L218-L225

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
open Formalism.FourierDecayAlt.P.A5x5
variable {K : Type} [CommRing K] {m : ℕ} (ψ : AddChar K ℂ)

theorem Formalism.FourierDecayAlt.P.A6x6.dot_perp {L : AddSubgroup K} {x u : Fin m → K} (hx : x ∈ PL L m)
    (hu : u ∈ PL (perp ψ L) m) : ψ (x ⬝ᵥ u) = 1 := by sorry
