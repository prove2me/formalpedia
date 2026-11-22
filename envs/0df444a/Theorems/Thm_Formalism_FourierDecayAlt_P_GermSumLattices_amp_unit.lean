-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_amp_unit
-- name    : Formalism.FourierDecayAlt.P.GermSumLattices.amp_unit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:55:57.297572+00:00
-- url     : https://prove2.me/theorems/89e5b41b-8903-468a-9c39-71a8f362fced
-- title:
--   Germ Sum Lattices: amp unit
-- statement:
--   The Germ Sum Lattices construction uses the amp unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermSumLattices.lean#L261-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermSumLattices.lean#L261-L266

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermSumLattices
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
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermSumLattices
variable {K : Type} [CommRing K] (R : Subring K)
variable {R}
variable (R) (ψ : AddChar K ℂ) (m : ℕ) (γ : Kˣ → ℂ)

theorem Formalism.FourierDecayAlt.P.GermSumLattices.amp_unit (h h' : Point K) (t₁ ζ z : Kˣ) :
    amp R ψ m γ h h' t₁ ζ (z : K) = γ (z * t₁) * conj (γ (ζ * z * t₁)) *
      (((modK R ((m + 1 : ℕ) : K))⁻¹ * modK R (z : K) ^ (m ^ 2) : ℝ) : ℂ) *
      Kp R ψ (addBlock h (m + 1) z) (addBlock h' (m + 1) (ζ * z)) := by sorry
