-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_shape
-- name    : Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.pw_shape
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:10.394972+00:00
-- url     : https://prove2.me/theorems/6f478bcf-ed54-4023-a444-c7a6306b09ff
-- title:
--   Orbital Integral Reduction: pw shape
-- statement:
--   The Orbital Integral Reduction construction uses the pw shape property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L2353-L2404
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L2353-L2404

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {K : Type} [CommRing K]

theorem Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.pw_shape {m : ℕ} (hm : 1 ≤ m) (t c : K) (ξ : Fin m → K) (N : Pr (m + 1) → K) :
    Hm t c ξ (1 + EE N) = HH t (Fin.cons (t * lastE ξ) (xs (t • N)) : Fin (m + 1) → K)
      (ys (t • N) (pw_Mx t (1 + EE N) *ᵥ ξ + pw_bv c)) := by sorry
