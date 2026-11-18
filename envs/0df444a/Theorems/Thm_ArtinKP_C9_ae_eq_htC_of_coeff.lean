-- Prove2me | Theorems.Thm_ArtinKP_C9_ae_eq_htC_of_coeff
-- name    : ArtinKP.C9.ae_eq_htC_of_coeff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:03:34.676989+00:00
-- url     : https://prove2.me/theorems/65a81724-6ced-4285-97b1-01a2c6f1c62b
-- title:
--   ArtinKP.C9.ae_eq_htC_of_coeff: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.C9`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology`, `open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric`, `open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N`):
--
--   ```lean
--   theorem ae_eq_htC_of_coeff (Γ : Subgroup (SL(2, 𝓞 F)))
--       (h𝔫 : ∃ 𝔫 : Ideal (𝓞 F), 𝔫 ≠ ⊥ ∧
--         ∀ β ∈ 𝔫, ∃ γ : GammaN Γ, ((γ : Γ) : SL(2, 𝓞 F)) 0 1 = β)
--       {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D)
--       (hfund : ∀ x : InfinitePlace F → ℂ, ∃! γ : GammaN Γ, (fun w => x w + GammaN.shift γ w) ∈ D)
--       (n₀ : ℕ) (hn₀ : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n₀)
--       (f : X F → ℂ) (hf : Measurable f) (hinv : ∀ (γ : GammaN Γ) (P : X F), f (γ • P) = f P)
--       (hL2 : ∀ n : ℕ, MemLp f 2 ((X.vol F).restrict (X.box n)))
--       (hint : ∀ n : ℕ, IntegrableOn f (X.box n) (X.vol F)) (z s₁ : ℂ)
--       (h0 : ∀ n : ℕ, n₀ ≤ n → ∀ φ : (InfinitePlace F → ℝ) → ℂ, Measurable φ → (∀ v, ‖φ v‖ ≤ 1) →
--         cf D n φ f = z * cf D n φ (htC s₁))
--       (h1 : ∀ ν ∈ dualLat Γ, ν ≠ 0 → ∀ n : ℕ, n₀ ≤ n → ∀ φ : (InfinitePlace F → ℝ) → ℂ,
--         Measurable φ → (∀ v, ‖φ v‖ ≤ 1) →
--         ∫ P in X.box n, conj (stripFn D ν φ P) * f P ∂X.vol F = 0) :
--       f =ᵐ[X.vol F] fun P => z * htC s₁ P
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.X.H3`, `ArtinKP.X.X`, `ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX` and `ArtinKP.X.X.box` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.X.H3.instMeasurableSpace` and `ArtinKP.X.X.vol` (definitions bundle `ArtinKPB006` of this split); `ArtinKP.N.cf`, `ArtinKP.RF.stripFn`, `ArtinKP.X.GammaN` and `ArtinKP.X.GammaN.shift` (definitions bundle `ArtinKPB015` of this split); `ArtinKP.N.htC` and `ArtinKP.RF.dualLat` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proofs of `ArtinKP.C9.theta_eq_zero_of_forall_tau_eq_zero`, `ArtinKP.G2a.thetaT_translate` and `ArtinKP.GK.hne` of this split import it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeSModel
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_ArtinKPB017

section

attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C9

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F]
  {Γ : Subgroup (SL(2, 𝓞 F))}

theorem ae_eq_htC_of_coeff (Γ : Subgroup (SL(2, 𝓞 F)))
    (h𝔫 : ∃ 𝔫 : Ideal (𝓞 F), 𝔫 ≠ ⊥ ∧
      ∀ β ∈ 𝔫, ∃ γ : GammaN Γ, ((γ : Γ) : SL(2, 𝓞 F)) 0 1 = β)
    {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D)
    (hfund : ∀ x : InfinitePlace F → ℂ, ∃! γ : GammaN Γ, (fun w => x w + GammaN.shift γ w) ∈ D)
    (n₀ : ℕ) (hn₀ : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n₀)
    (f : X F → ℂ) (hf : Measurable f) (hinv : ∀ (γ : GammaN Γ) (P : X F), f (γ • P) = f P)
    (hL2 : ∀ n : ℕ, MemLp f 2 ((X.vol F).restrict (X.box n)))
    (hint : ∀ n : ℕ, IntegrableOn f (X.box n) (X.vol F)) (z s₁ : ℂ)
    (h0 : ∀ n : ℕ, n₀ ≤ n → ∀ φ : (InfinitePlace F → ℝ) → ℂ, Measurable φ → (∀ v, ‖φ v‖ ≤ 1) →
      cf D n φ f = z * cf D n φ (htC s₁))
    (h1 : ∀ ν ∈ dualLat Γ, ν ≠ 0 → ∀ n : ℕ, n₀ ≤ n → ∀ φ : (InfinitePlace F → ℝ) → ℂ,
      Measurable φ → (∀ v, ‖φ v‖ ≤ 1) →
      ∫ P in X.box n, conj (stripFn D ν φ P) * f P ∂X.vol F = 0) :
    f =ᵐ[X.vol F] fun P => z * htC s₁ P := by
  sorry

end

end ArtinKP.C9
end
