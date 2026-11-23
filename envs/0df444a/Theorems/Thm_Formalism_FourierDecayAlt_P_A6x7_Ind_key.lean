-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x7_Ind_key
-- name    : Formalism.FourierDecayAlt.P.A6x7.Ind.key
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:06:11.490332+00:00
-- url     : https://prove2.me/theorems/bd8d3840-a54a-4cfb-b514-b6079a9a96bc
-- title:
--   Ind: key
-- statement:
--   The Ind construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussIndexIndependentOfChoice.lean#L825-L909
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussIndexIndependentOfChoice.lean#L825-L909

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x7 Formalism.FourierDecayAlt.P.A6x7.Ind
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ} {m : ℕ}

theorem Formalism.FourierDecayAlt.P.A6x7.Ind.key (h2 : IsUnit (2 : K)) {M : Matrix (Fin m) (Fin m) K} (hM : M.IsSymm)
    (hdet : IsUnit M.det) {L L₂ Λ₀ : AddSubgroup K} (hL : IsLat L) (hL₂ : IsLat L₂)
    (hΛ₀ : IsLat Λ₀) (hle : L ≤ L₂) (hΛL : Λ₀ ≤ L) (hperp : perp ψ (perp ψ L) = L)
    (hA : GaussAdm ψ L M) (hI : LatInvN Λ₀ (gaussF ψ L M)) (hI₂ : LatInvN Λ₀ (gaussF ψ L₂ M)) :
    ∑ᶠ y : Fin m → K ⧸ Λ₀, gaussF ψ L₂ M (fun i => Quotient.out (y i)) =
      ∑ᶠ y : Fin m → K ⧸ Λ₀, gaussF ψ L M (fun i => Quotient.out (y i)) := by sorry
