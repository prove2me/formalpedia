-- Prove2me | Theorems.Thm_AutomorphicForm_finsum_setIntegral_sigmaSectionActOn_convOp_mul_conj_eq_finsum_setIntegral_twistedConvOp_mul_conj_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.finsum_setIntegral_sigmaSectionActOn_convOp_mul_conj_eq_finsum_setIntegral_twistedConvOp_mul_conj_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/904ad29b-acbc-5a53-b616-4eef92fce4a2
-- title:
--   Moving the σ-twist across the convolution in block pairings
-- statement:
--   Let $L/K$ be an extension of number fields, let $D$ consist of a homomorphism from $\mathrm{Aut}_K(L)$ to the ring automorphisms of $\mathbb{A}_L$ that is continuous and compatible with the embedding of $L$, let $\sigma$ be a $K$-automorphism of $L$, and write $\sigma_{\mathbb{A}}$ for the induced automorphism of $\mathrm{GL}_2(\mathbb{A}_L)$ given by $D.\mathrm{act}\,\sigma$ entrywise. Let $0<\alpha<\beta$ and let $\Phi$ be a subset of $\mathrm{GL}_2(\mathbb{A}_L)$ contained in the slab $\{g \mid \lVert\det g\rVert \in [\alpha,\beta]\}$, where $\lVert\cdot\rVert$ is the module of the idele acting on $\mathbb{A}_L$, which is a fundamental domain for the image of $\mathrm{GL}_2(L)$ acting on the slab with the restricted Haar measure $\mu$ of $\mathrm{GL}_2(\mathbb{A}_L)$. Let $\xi$ be a character of the full idele group of $L$, let $S_L$ be a finite set of finite places of $L$ that is a union of fibres over $K$ (membership depends only on the prime of $\mathcal{O}_K$ below), let $N$ be an ideal of $\mathcal{O}_L$ all of whose prime divisors lie in $S_L$, and let $\mathrm{tys}_L$ assign to each infinite place of $L$ a finite family of archimedean representation types. Take the carrier data consisting of $\mu$, the domain $\Phi$, the full central subgroup, the level family $M \mapsto$ (principal level $M$) $\cap$ (finite-adelic subgroup), the Hecke generators $\mathrm{heckeGen}$, and the additive Haar measure of $\mathbb{A}_L$ conditioned on the adelic box. Let $b : \iota \to (\mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C})$ and $\mathrm{cls} : \iota \to$ Hecke eigensystems be such that each $\mathrm{cls}\,i$ is a cuspidal class for these data (level $N$, vanishing eigenvalue and central data at $S_L$, nonzero isotypic space) and $b\,i$ lies in the isotypic cusp submodule of $\mathrm{cls}\,i$ intersected with the archimedean cut submodule for $\mathrm{tys}_L$; suppose $\int_\Phi b\,i \cdot \overline{b\,i}\,d\mu = 1$ and $\int_\Phi b\,i \cdot \overline{b\,j}\,d\mu = 0$ for $i \neq j$, and that for every cuspidal class $\pi$ the fibre $\{i \mid \mathrm{cls}\,i = \pi\}$ is finite and the $b\,i$ over it span the cut isotypic space of $\pi$. Let $f$ be continuous with compact support, invariant on both sides under (principal level $N$) $\cap$ (finite-adelic subgroup), and archimedean bi-finite for $\mathrm{tys}_L$ in the sense that $x \mapsto f(x^{-1})$ lies in the archimedean cut submodule and $f$ in the archimedean dual cut submodule. Then for every cuspidal class $\Psi$ the finite sums over $\{i \mid \mathrm{cls}\,i = \Psi\}$ of $\int_\Phi \bigl(\int f(y)\, b\,i(\sigma_{\mathbb{A}}(x)\,y)\,d\mu(y)\bigr)\overline{b\,i(x)}\,d\mu(x)$ and of $\int_\Phi \bigl(\int f(y)\, b\,i(\sigma_{\mathbb{A}}(x\,y))\,d\mu(y)\bigr)\overline{b\,i(x)}\,d\mu(x)$ agree, that is, applying $\sigma$ after right convolution by $f$ and convolving the $\sigma$-translate of $b\,i$ by $f$ give the same diagonal pairing sum over the block of $\Psi$.
--
--   This is the interchange step in the twisted trace computation for base change: inside a single Hecke block the Galois twist may be moved from outside the convolution operator $R(f)$ to its argument without changing the diagonal sum of pairings against the orthonormal basis. It is used in the identification of such sums with the twisted cut trace of $f$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_finsum_setIntegral_sigmaSectionActOn_convOp_mul_conj_eq_finsum_setIntegral_twistedConvOp_mul_conj_of_orthonormal_principalLevel_of_isFundamentalDomain_slab.lean

import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.finsum_setIntegral_sigmaSectionActOn_convOp_mul_conj_eq_finsum_setIntegral_twistedConvOp_mul_conj_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (Φ : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (ι : Type) (b : ι → AdelicGL2 (𝓞 L) L → ℂ) (cls : ι → HeckeEigensystem L ℂ)
    (hb : ∀ i, cls i ∈ cuspClasses L
        (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ N SL ∧
      b i ∈ isotypicCuspSubmodule L
        (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ N SL (cls i) ⊓ archCutSubmodule L tysL)
    (hb₁ : ∀ i, ∫ g in Φ, b i g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = 1)
    (hb₀ : ∀ i j, i ≠ j → ∫ g in Φ, b i g * conj (b j g) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = 0)
    (hbs : ∀ π ∈ cuspClasses L
        (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ N SL,
      {i | cls i = π}.Finite ∧
      Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule L
        (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ N SL π ⊓ archCutSubmodule L tysL)
    (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfU : IsBiInvariantUnder L (principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) f)
    (hft : IsArchBiFinite L tysL f)
    (Ψ : HeckeEigensystem L ℂ)
    (hΨ : Ψ ∈ cuspClasses L
        (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ N SL) :
    ∑ᶠ i : {i // cls i = Ψ},
        ∫ x in Φ, sigmaSectionActOn K L D σ (convOp L f (b i)) x * conj (b i x)
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
      ∑ᶠ i : {i // cls i = Ψ},
        ∫ x in Φ, twistedConvOp K L D σ f (b i) x * conj (b i x)
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L) := by sorry
