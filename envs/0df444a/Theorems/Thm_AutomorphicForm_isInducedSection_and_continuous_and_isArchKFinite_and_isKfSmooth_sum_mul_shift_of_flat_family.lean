-- Prove2me | Theorems.Thm_AutomorphicForm_isInducedSection_and_continuous_and_isArchKFinite_and_isKfSmooth_sum_mul_shift_of_flat_family
-- name    : AutomorphicForm.isInducedSection_and_continuous_and_isArchKFinite_and_isKfSmooth_sum_mul_shift_of_flat_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/ae951eae-dfd6-5c99-9994-d40c617edb0a
-- title:
--   Entire combinations and imaginary shifts of flat induced-section families
-- statement:
--   Let $K$ be a number field, $N$ an ideal of $\mathcal O_K$, and $\mathrm{tysK}$ an archimedean type family on $K$ (a number $\mathrm{card}\,w$ of types together with representations $\mathrm{rep}\,w\,i$ for each infinite place $w$). Let $\alpha_m$ be the character of the idele units obtained from the module character $\mathrm{distribHaarChar}$ of the adele ring of $K$, viewed in $\mathbb R^\times$, and assume $\alpha_m$ is everywhere positive. Let $\mu,\nu$ be characters of the idele units with values in $\mathbb C^\times$, let $n\in\mathbb N$ and let $\varphi_j\colon\mathbb C\to \mathrm{GL}_2(\mathbb A_K)\to\mathbb C$, $j<n$, satisfy: for all $j,s$, $\varphi_j(s)$ is an induced section for the pair $(\mu\cdot\alpha_m^{\,s+1/2},\ \nu\cdot\alpha_m^{-(s+1/2)})$, i.e. $\varphi_j(s)(bg)$ equals the product of the two characters evaluated on the diagonal entries of $b$ times $\varphi_j(s)(g)$ for $b$ in the adelic Borel subgroup; $\varphi_j(s)$ is archimedean $K$-finite at every infinite place and $K_f$-smooth (a smooth vector for right translation by the kernel of the archimedean projection); $(s,g)\mapsto\varphi_j(s)(g)$ is continuous and $s\mapsto\varphi_j(s)(g)$ is entire; for each infinite place $w$ there is a finite-dimensional $\mathbb C$-subspace $W$ of functions on the row-isometry subgroup at $w$ containing every right translate $k\mapsto\varphi_j(s)(gk)$; $\varphi_j(s)$ and $\varphi_j(0)$ agree on the adelic maximal compact subgroup; $\varphi_j(s)$ is right invariant under $\mathrm{principalLevel}\,N$ intersected with the finite subgroup; and $\varphi_j(s)$ lies in the archimedean cut submodule $\mathrm{archCutSubmodule}\,K\,\mathrm{tysK}$. Finally let $\tau\in\mathbb R$ and let $c_j\colon\mathbb C\to\mathbb C$ be entire. Then $\psi(s)(g)=\sum_j c_j(s)\,\varphi_j(s+i\tau)(g)$ satisfies all of the same properties with the inducing pair twisted: $\psi(s)$ is an induced section for $(\mu\cdot\mathrm{normPowChar}\,K\,\tau,\ \nu\cdot(\mathrm{normPowChar}\,K\,\tau)^{-1})$ at parameter $s$, $(s,g)\mapsto\psi(s)(g)$ is continuous, $s\mapsto\psi(s)(g)$ is entire, each $\psi(s)$ is archimedean $K$-finite and $K_f$-smooth, the uniform finite-dimensional span condition holds at every infinite place, $\psi(s)$ is right invariant under $\mathrm{principalLevel}\,N$ intersected with the finite subgroup, and $\psi(s)$ lies in $\mathrm{archCutSubmodule}\,K\,\mathrm{tysK}$.
--
--   This records that the class of admissible families of induced sections at a fixed level and fixed archimedean types is closed under entire scalar combinations together with a purely imaginary shift of the inducing parameter, the shift being absorbed into the unitary twist $(\,|\cdot|^{i\tau},|\cdot|^{-i\tau})$ of the inducing pair via [`AutomorphicForm.etaFst_etaSnd_mul_normPowChar_eq_shift`](thm.html#AutomorphicForm.etaFst_etaSnd_mul_normPowChar_eq_shift). It is used in the construction of matched Paley–Wiener families of sections for the analytic input to the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isInducedSection_and_continuous_and_isArchKFinite_and_isKfSmooth_sum_mul_shift_of_flat_family.lean

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

open AutomorphicForm

theorem AutomorphicForm.isInducedSection_and_continuous_and_isArchKFinite_and_isKfSmooth_sum_mul_shift_of_flat_family
    (K : Type) [Field K] [NumberField K] (N : Ideal (𝓞 K)) (tysK : ArchTypeFamily K) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (n : ℕ)
      (φE : Fin n → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ j s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φE j s))
      (_hφEK : ∀ j s, IsArchKFinite K (φE j s))
      (_hφEf : ∀ j s, IsKfSmooth K (φE j s))
      (_hφEjc : ∀ j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE j p.1 p.2))
      (_hφEhol : ∀ j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φE j s g))
      (_hφEKu : ∀ j (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φE j s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφEflat : ∀ j (s : ℂ) (k : adelicMaximalCompact K),
        φE j s (k : AdelicGL2 (𝓞 K) K) = φE j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφElev : ∀ j (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φE j s (g * u) = φE j s g)
      (_hφEty : ∀ j (s : ℂ), φE j s ∈ archCutSubmodule K tysK)
      (τ : ℝ) (c : Fin n → ℂ → ℂ) (_hc : ∀ j, Differentiable ℂ (c j)),
    let ψ : ℂ → AdelicGL2 (𝓞 K) K → ℂ := fun s g => ∑ j, c j s * φE j (s + (τ : ℂ) * Complex.I) g
    (∀ s, IsInducedSection (𝓞 K) K (etaFst (μ * NumberField.TateGlobal.normPowChar K τ) αm hαm s)
        (etaSnd (ν * (NumberField.TateGlobal.normPowChar K τ)⁻¹) αm hαm s) (ψ s)) ∧
    Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψ p.1 p.2) ∧
    (∀ g : AdelicGL2 (𝓞 K) K, Differentiable ℂ (fun s => ψ s g)) ∧
    (∀ s, IsArchKFinite K (ψ s)) ∧
    (∀ s, IsKfSmooth K (ψ s)) ∧
    (∀ w : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψ s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W) ∧
    (∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψ s (g * u) = ψ s g) ∧
    (∀ s, ψ s ∈ archCutSubmodule K tysK) := by sorry
