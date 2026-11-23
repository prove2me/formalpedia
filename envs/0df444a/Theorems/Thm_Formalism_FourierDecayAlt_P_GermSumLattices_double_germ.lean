-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_double_germ
-- name    : Formalism.FourierDecayAlt.P.GermSumLattices.double_germ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:42.049996+00:00
-- url     : https://prove2.me/theorems/d9f72f31-8f43-4fc3-a12f-64f7038b3c70
-- title:
--   Germ Sum Lattices: double germ
-- statement:
--   The Germ Sum Lattices construction uses the double germ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermSumLattices.lean#L116-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermSumLattices.lean#L116-L155

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

theorem Formalism.FourierDecayAlt.P.GermSumLattices.double_germ (h h' : Point K) (t₁ t₂ κ : Kˣ) (cr : K ⧸ R.toAddSubgroup → Kˣ) (S : Set K)
    (μ : Finset Kˣ) (hμ : ∀ ζ : Kˣ, ζ ∈ μ ↔ ζ ^ (m + 1) = 1)
    (hSfin : {x | (cr x : K) ∈ S}.Finite)
    (hroots : ∀ D : Kˣ, {z : Kˣ | z ^ (m + 1) = D}.Finite)
    (hherm : ∀ w w' : Point K, Kp R ψ w' w = conj (Kp R ψ w w'))
    (hG1 : ∀ x, (cr x : K) ∈ S → ∀ w', Kp R ψ (pt2 h m t₁ (cr x)) w' =
      germSum R ψ m γ t₁ (cr x) (fun z => Kp R ψ (addBlock h (m + 1) z) w'))
    (hG2 : ∀ x, (cr x : K) ∈ S → ∀ w', Kp R ψ (pt2 h' m t₂ (cr x)) w' =
      germSum R ψ m γ t₂ (cr x) (fun z => Kp R ψ (addBlock h' (m + 1) z) w'))
    (hκ : κ ^ (m + 1) = (t₂ * t₁⁻¹) ^ m) :
    uGram R ψ m cr S h h' t₁ t₂ =
      ((modK R ((t₁ : K) * (t₂ : K)) ^ (m * (m + 1) / 2) : ℝ) : ℂ) *
      ((((modK R (t₁ : K) ^ (-((m : ℝ) ^ 2) / 2) : ℝ) : ℂ) *
        ((modK R (t₂ : K) ^ (-((m : ℝ) ^ 2) / 2) : ℝ) : ℂ)) *
      ∑ ζ ∈ μ, ∑ x ∈ hSfin.toFinset, ∑ z ∈ (hroots ((-t₁) ^ m * cr x)).toFinset,
        germCoef R ψ m γ t₁ z * conj (germCoef R ψ m γ t₂ (ζ * κ * z)) *
          Kp R ψ (addBlock h (m + 1) z) (addBlock h' (m + 1) (ζ * κ * z))) := by sorry
