-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_bx_sum
-- name    : Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.bx_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:35.691728+00:00
-- url     : https://prove2.me/theorems/8057becb-656d-4559-9f39-798207acbc01
-- title:
--   Orbital Integral Reduction: bx sum
-- statement:
--   The Orbital Integral Reduction construction uses the bx sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L378-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L378-L396

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
variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}

theorem Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.bx_sum (_hD : LocalDatum K R ψ) {ι κ : Type} [Fintype ι] [Fintype κ] {Λ L : AddSubgroup K}
    (hΛ : IsLat Λ) (hL : IsLat L) (f : (ι ⊕ κ → K) → ℂ) (hs : BSupp L f) :
    bx R Λ (ι ⊕ κ) f = bx R Λ ι (fun a => bx R Λ κ (fun b => f (Sum.elim a b))) := by sorry
