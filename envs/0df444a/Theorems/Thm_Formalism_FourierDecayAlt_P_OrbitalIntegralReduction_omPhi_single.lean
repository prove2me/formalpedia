-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_omPhi_single
-- name    : Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.omPhi_single
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:34.188738+00:00
-- url     : https://prove2.me/theorems/74c501a6-8440-4eb3-b177-40bac45e242f
-- title:
--   Orbital Integral Reduction: om Phi single
-- statement:
--   The Orbital Integral Reduction construction uses the om Phi single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L1178-L1202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L1178-L1202

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
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}

theorem Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.omPhi_single (n : ℕ) (z : Kˣ) (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ) :
    omPhi R ψ (addBlock h0 n z) Φ = ∑ᶠ q : upUniG K n ⧸ intSub R (upUniG K n),
      Φ n (((z : K) • sec_m (Quotient.out q)).submatrix Fin.rev id) *
        ψ (sUp (sec_m (Quotient.out q))) := by sorry
