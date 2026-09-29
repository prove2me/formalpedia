-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_eq_mul_normPowChar_and_eq_mul_normPowChar_inv_of_pairs_of_exists_isInducedSection
-- name    : AutomorphicForm.exists_forall_eq_mul_normPowChar_and_eq_mul_normPowChar_inv_of_pairs_of_exists_isInducedSection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/afa3963b-73a3-50c5-bed4-270c1f99af89
-- title:
--   Second family of Eisenstein pairs as norm twists
-- statement:
--   Let $K$ be a number field, let $\xi_K$ be a character of the full subgroup of $\mathbb{A}_K^\times$ with values in $\mathbb{C}^\times$, let $N$ be an ideal of $\mathcal{O}_K$ and $\mathcal{T}$ an archimedean type family (a number $c(w)$ of representations $\mathrm{rep}(w,j)$ at each infinite place $w$). Write $\alpha$ for the character of $\mathbb{A}_K^\times$ obtained from the module `distribHaarChar` of the adele ring, viewed in $\mathbb{R}^\times$, assumed everywhere positive. Given an index type $\iota_E$ and families $\mu,\nu:\iota_E\to\operatorname{Hom}(\mathbb{A}_K^\times,\mathbb{C}^\times)$ whose members are unitary ($\|\chi(x)\|=1$ for all $x$), trivial on the image of $K^\times$, continuous, and satisfy $\mu_e\nu_e=\xi_K$; assume the completeness property that for every pair $(\mu',\nu')$ with the same four properties, every $t\in\mathbb{R}$ and every nonzero continuous $\varphi_0:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ which transforms under the adelic Borel by $\mu'\alpha^{it+1/2}$ on the first and $\nu'\alpha^{-(it+1/2)}$ on the second diagonal entry, is $K_\infty$-finite at every infinite place, is right invariant under $\mathrm{principalLevel}(N)$ intersected with the kernel of the archimedean projection, and lies in the archimedean type submodule cut out by $\mathcal{T}$, there is $e$ with $\mu_e=\mu'$ and $\nu_e=\nu'$ on the norm-one ideles (the kernel of `distribHaarChar`). Given a second such family $(\mu^P_i,\nu^P_i)_{i\in\iota_P}$ each member of which carries such a section for some $t$, the conclusion is that there are maps $em:\iota_P\to\iota_E$ and $\tau:\iota_P\to\mathbb{R}$ with $\mu^P_i=\mu_{em(i)}\cdot\|\cdot\|^{i\tau_i}$ and $\nu^P_i=\nu_{em(i)}\cdot\|\cdot\|^{-i\tau_i}$ for all $i$, where $\|\cdot\|^{i\tau}$ denotes `normPowChar`.
--
--   This is the rigidity step which identifies a second, a priori unrelated, family of inducing data for continuous-spectrum Eisenstein pairs with a unitary norm twist of a family already known to be complete for the given level and archimedean types; it rests on the classification of continuous unitary idele class characters trivial on the norm-one ideles. It is used in the Paley–Wiener matching and orthogonality arguments for pseudo-Eisenstein series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_eq_mul_normPowChar_and_eq_mul_normPowChar_inv_of_pairs_of_exists_isInducedSection.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_NumberField_NormPowChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_eq_mul_normPowChar_and_eq_mul_normPowChar_inv_of_pairs_of_exists_isInducedSection
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 K)) (tysK : ArchTypeFamily K) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (ιE : Type)
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ), μ e z * ν e z = ξK ⟨z, Subgroup.mem_top z⟩)
      (_hpairs : ∀ (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        IsUnitaryChar (𝓞 K) K μ' → IsUnitaryChar (𝓞 K) K ν' →
        IsIdeleClassChar (𝓞 K) K μ' → IsIdeleClassChar (𝓞 K) K ν' →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ' z : ℂˣ) : ℂ)) →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν' z : ℂˣ) : ℂ)) →
        (∀ z : (AdeleRing (𝓞 K) K)ˣ, μ' z * ν' z = ξK ⟨z, Subgroup.mem_top z⟩) →
        ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μ' αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK → φ₀ ≠ 0 →
        ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z = μ' z ∧ ν e z = ν' z)
      (ιP : Type)
      (μP νP : ιP → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμP : ∀ i, IsUnitaryChar (𝓞 K) K (μP i)) (_hνP : ∀ i, IsUnitaryChar (𝓞 K) K (νP i))
      (_hμPic : ∀ i, IsIdeleClassChar (𝓞 K) K (μP i)) (_hνPic : ∀ i, IsIdeleClassChar (𝓞 K) K (νP i))
      (_hμPc : ∀ i, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μP i z : ℂˣ) : ℂ))
      (_hνPc : ∀ i, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((νP i z : ℂˣ) : ℂ))
      (_hμνP : ∀ (i : ιP) (z : (AdeleRing (𝓞 K) K)ˣ), μP i z * νP i z = ξK ⟨z, Subgroup.mem_top z⟩)
      (_hsec : ∀ i : ιP, ∃ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst (μP i) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (νP i) αm hαm ((t : ℂ) * Complex.I)) φ₀ ∧
        Continuous φ₀ ∧ IsArchKFinite K φ₀ ∧
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) ∧
        φ₀ ∈ archCutSubmodule K tysK ∧ φ₀ ≠ 0),
    ∃ (em : ιP → ιE) (τ : ιP → ℝ),
      ∀ i : ιP, μP i = μ (em i) * NumberField.TateGlobal.normPowChar K (τ i) ∧
        νP i = ν (em i) * (NumberField.TateGlobal.normPowChar K (τ i))⁻¹ := by sorry
