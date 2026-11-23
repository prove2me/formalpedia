-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_st_blk_Hm
-- name    : Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.st_blk_Hm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:21.397811+00:00
-- url     : https://prove2.me/theorems/739f5370-d7ea-4561-a469-b079f08d36e8
-- title:
--   Orbital Integral Reduction: st blk Hm
-- statement:
--   The Orbital Integral Reduction construction uses the st blk Hm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L1139-L1169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L1139-L1169

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

theorem Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.st_blk_Hm (m : ℕ) (t : Kˣ) (c : K) (ξ : Fin m → K)
    (u : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (hu : IsUpUni u) :
    blkM (rfl : m + 1 = m + 1) (antidiagonalBlock m t) 0 (ξ ᵥ* antidiagonalBlock m t) c * u =
      (Hm (t : K) c ξ u).submatrix Fin.rev id := by sorry
