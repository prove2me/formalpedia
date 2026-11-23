-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_tk_ind_fin
-- name    : Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.tk_ind_fin
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:41.492364+00:00
-- url     : https://prove2.me/theorems/c0d51a06-66db-41d9-80fa-ba34e5adae14
-- title:
--   Orbital Integral Reduction: tk ind fin
-- statement:
--   The Orbital Integral Reduction construction uses the tk ind fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L568-L578
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L568-L578

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
variable {V : Type} [AddCommGroup V]
variable [TopologicalSpace V] [IsTopologicalAddGroup V]
open Classical

theorem Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.tk_ind_fin {V₀ N M' : AddSubgroup V} (h0 : Lat V₀) (hN : Lat N) (hM' : Lat M')
    (hle : M' ≤ N) (c : V) :
    (Function.support fun y : V ⧸ M' =>
      (if (Quotient.out y : V) - c ∈ N then (1 : ℂ) else 0)).Finite := by sorry
