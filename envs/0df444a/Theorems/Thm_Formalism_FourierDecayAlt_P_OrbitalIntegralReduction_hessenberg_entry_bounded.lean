-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_hessenberg_entry_bounded
-- name    : Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.hessenberg_entry_bounded
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:07.396308+00:00
-- url     : https://prove2.me/theorems/0a5cc1da-1d9e-4eff-8b33-6eeeafe11130
-- title:
--   Orbital Integral Reduction: hessenberg entry bounded
-- statement:
--   The Orbital Integral Reduction construction uses the hessenberg entry bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L2019-L2028
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L2019-L2028

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
  {ψ : AddChar K ℂ} {ϖ : Kˣ} {L₀ Λ₀ : AddSubgroup K} {Q : Set K} {a b : ℕ}

theorem Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.hessenberg_entry_bounded (hϖ : (ϖ : K) ∈ R) {m : ℕ} {t ρ : K} {x : Fin m → K} {y : Pr (m + 1) → K}
    (ht : Bd R ϖ a t) (hx : ∀ k, Bd R ϖ a (x k)) (i : Fin (m + 1)) (j : Fin m)
    (hy : ∀ h : i < j.succ, Bd R ϖ a (y ⟨(i, j.succ), h⟩)) :
    Bd R ϖ a (HH t (Fin.cons ρ x : Fin (m + 1) → K) y i j.succ) := by sorry
