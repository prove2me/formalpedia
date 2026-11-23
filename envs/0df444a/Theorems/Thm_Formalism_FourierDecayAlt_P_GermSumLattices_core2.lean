-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_core2
-- name    : Formalism.FourierDecayAlt.P.GermSumLattices.core2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:40.315333+00:00
-- url     : https://prove2.me/theorems/df6e6cb5-e748-4482-9da9-07b3efe12961
-- title:
--   Germ Sum Lattices: core2
-- statement:
--   The Germ Sum Lattices construction uses the core2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermSumLattices.lean#L339-L453
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermSumLattices.lean#L339-L453

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
variable {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ) (m : ℕ) (γ : Kˣ → ℂ)
open Classical

theorem Formalism.FourierDecayAlt.P.GermSumLattices.core2 (hMM : MM R) (hun : ∀ x : K, conj (ψ x) = ψ (-x)) (hψR : ∀ r ∈ R, ψ r = 1)
    (hs : IsUnit ((m + 1 : ℕ) : K)) (hγ1 : ∀ a, ‖γ a‖ = 1)
    (hγ2 : ∀ a b : Kˣ, γ (a * b ^ 2) = γ a)
    (h h' : Point K) (t₁ t₂ κ : Kˣ) (cr : K ⧸ R.toAddSubgroup → Kˣ) (S Om : Set K)
    (μ : Finset Kˣ) (hμ : ∀ ζ : Kˣ, ζ ∈ μ ↔ ζ ^ (m + 1) = 1)
    (hSfin : {x | (cr x : K) ∈ S}.Finite)
    (hroots : ∀ D : Kˣ, {z : Kˣ | z ^ (m + 1) = D}.Finite)
    (hherm : ∀ w w' : Point K, Kp R ψ w' w = conj (Kp R ψ w w'))
    (hG1 : ∀ x, (cr x : K) ∈ S → ∀ w', Kp R ψ (pt2 h m t₁ (cr x)) w' =
      germSum R ψ m γ t₁ (cr x) (fun z => Kp R ψ (addBlock h (m + 1) z) w'))
    (hG2 : ∀ x, (cr x : K) ∈ S → ∀ w', Kp R ψ (pt2 h' m t₂ (cr x)) w' =
      germSum R ψ m γ t₂ (cr x) (fun z => Kp R ψ (addBlock h' (m + 1) z) w'))
    (hκ : κ ^ (m + 1) = (t₂ * t₁⁻¹) ^ m)
    (hT : modK R (t₂ : K) = modK R (t₁ : K))
    (b : Kˣ) (hb : κ * t₂ * t₁⁻¹ = b ^ 2)
    (hmem : ∀ x, (cr x : K) ∈ S → ∀ z : Kˣ, z ^ (m + 1) = (-t₁) ^ m * cr x → (z : K) ∈ Om)
    (hμOm : ∀ z ∈ Om, ∀ ζ ∈ μ, (ζ : K) * z ∈ Om)
    (hLCκ : ∀ z : Kˣ, (z : K) ∈ Om → ∀ w', Kp R ψ (addBlock h' (m + 1) (κ * z)) w' =
      Kp R ψ (addBlock h' (m + 1) z) w')
    (d : K) (hphase : ∀ z ∈ Om, ((m + 1 : ℕ) : K) * z * ((t₁⁻¹ : Kˣ) : K) -
      ((m + 1 : ℕ) : K) * ((κ : K) * z) * ((t₂⁻¹ : Kˣ) : K) - z * d ∈ R)
    (hX : ∀ ζ ∈ μ, ζ ≠ 1 → ∑ᶠ x : K ⧸ R.toAddSubgroup, (if (cr x : K) ∈ S then
        ∑ᶠ z : Kˣ, if z ^ (m + 1) = (-t₁) ^ m * cr x then
          amp R ψ m γ h h' t₁ ζ (z : K) * ψ (((m + 1 : ℕ) : K) * (z : K) * ((t₁⁻¹ : Kˣ) : K) -
            ((m + 1 : ℕ) : K) * ((ζ : K) * (κ : K) * (z : K)) * ((t₂⁻¹ : Kˣ) : K)) else 0
        else 0) = 0)
    (I : ℂ)
    (hCV : ∑ᶠ x : K ⧸ R.toAddSubgroup, (if (cr x : K) ∈ S then
        ∑ᶠ z : Kˣ, if z ^ (m + 1) = (-t₁) ^ m * cr x then f1 R ψ m h h' d (z : K) else 0
        else 0) =
      (((modK R (t₁ : K) ^ m)⁻¹ * modK R ((m + 1 : ℕ) : K) : ℝ) : ℂ) *
        ((((modK R ((m + 1 : ℕ) : K))⁻¹ : ℝ) : ℂ) * I)) :
    uGram R ψ m cr S h h' t₁ t₂ = I := by sorry
