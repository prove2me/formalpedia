-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_centralEllipticFold_eq_finsum_inv_card_mul_integral_setIntegral_centralizerDomain
-- name    : AutomorphicForm.setIntegral_centralEllipticFold_eq_finsum_inv_card_mul_integral_setIntegral_centralizerDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/fbb31e1e-080c-5115-b4bc-9ac02c03c159
-- title:
--   Unfolding the central and elliptic terms of the adelic GL₂ kernel
-- statement:
--   Let $F$ be a number field, with $\mathbb{A}$ its adele ring and $\mathrm{GL}_2(\mathbb{A})$ the adelic group, equipped with its Borel structure and the Haar measure `adelicGLHaar`. Let $0<\alpha<\beta$ be reals and write $S=\{g : \|\det g\|_{\mathbb{A}}\in[\alpha,\beta]\}$ for the slab cut out by the idele norm (the `distribHaarChar` of the determinant). Assume: $\Phi\subseteq S$ is a fundamental domain for the image of $\mathrm{GL}_2(F)$ in $\mathrm{GL}_2(\mathbb{A})$ with respect to the Haar measure restricted to $S$; $\nu_Z$ is a Haar measure on the idele group $\mathbb{A}^\times$ and $\Omega$ a fundamental domain for the image of $F^\times$ in $\mathbb{A}^\times$ for $\nu_Z$; $\xi$ is a homomorphism from the full subgroup of $\mathbb{A}^\times$ to $\mathbb{C}^\times$, continuous as a $\mathbb{C}$-valued function and trivial on principal ideles; $f:\mathrm{GL}_2(\mathbb{A})\to\mathbb{C}$ is continuous with compact support; $R$ is a subset of the union of the central cell (those $\gamma\in\mathrm{GL}_2(F)$ whose matrix is a scalar multiple of the identity) and the elliptic cell (those whose characteristic polynomial has no root in $F$), such that every element $\gamma$ of that union admits a unique $\gamma_0\in R$ with $\gamma=\mathrm{scalar}(a)\,h^{-1}\gamma_0 h$ for some $h\in\mathrm{GL}_2(F)$, $a\in F^\times$; and for each $\gamma_0\in R$, $\Psi(\gamma_0)\subseteq S$ is a fundamental domain, for the Haar measure restricted to $S$, for the image in $\mathrm{GL}_2(\mathbb{A})$ of the centraliser of $\gamma_0$ in $\mathrm{GL}_2(F)$. Then the integral over $x\in\Phi$ of $\int_{z\in\Omega}\xi(z)\bigl(\sum_{\gamma\ \mathrm{central}}f(x^{-1}\gamma z x)+\sum_{\gamma\ \mathrm{elliptic}}f(x^{-1}\gamma z x)\bigr)\,d\nu_Z$, the two inner sums being the central and elliptic parts of the adelic kernel of $f$ evaluated at $(x,zx)$, equals the finite sum over $\gamma_0\in R$ of $|\{a\in F^\times : \mathrm{scalar}(a)\gamma_0=h^{-1}\gamma_0h \text{ for some } h\in\mathrm{GL}_2(F)\}|^{-1}$ times $\int_{\mathbb{A}^\times}\xi(z)\bigl(\int_{\Psi(\gamma_0)}f(x^{-1}\gamma_0 z x)\,dx\bigr)d\nu_Z$, the $z$-integral now being over the whole idele group.
--
--   This is the geometric unfolding of the central and elliptic contributions to the $\mathrm{GL}_2$ trace formula over a number field: the double integral of the $\xi$-twisted kernel over a fundamental domain is rewritten as a sum of orbital integrals over centraliser fundamental domains, weighted by the number of scalars $a$ for which $a\gamma_0$ is conjugate to $\gamma_0$. It feeds the later identification of the twisted elliptic–central fold with a sum over conjugacy representatives and its factorisation according to norm fibres.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_centralEllipticFold_eq_finsum_inv_card_mul_integral_setIntegral_centralizerDomain.lean

import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open IsDedekindDomain
attribute [local instance] NumberField.AdelicHaar.glBorel

theorem
AutomorphicForm.setIntegral_centralEllipticFold_eq_finsum_inv_card_mul_integral_setIntegral_centralizerDomain
    (F : Type) [Field F] [NumberField F] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (Φ : Set (AdelicGL2 (𝓞 F) F))
    (hΦs : Φ ⊆
      {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (νZ : Measure (AdeleRing (𝓞 F) F)ˣ) [νZ.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 F) F)ˣ)
    (hΩ : IsFundamentalDomain
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range Ω νZ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 F) F)ˣ,
      z ∈ (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (R : Set (GL (Fin 2) F)) (hRsub : R ⊆ AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F)
    (hR : ∀ γ ∈ AutomorphicForm.centralCell F ∪ AutomorphicForm.ellipticCell F, ∃! γ₀ : GL (Fin 2) F, γ₀ ∈ R ∧
      ∃ (h : GL (Fin 2) F) (a : Fˣ), γ = Matrix.GeneralLinearGroup.scalar (Fin 2) a * (h⁻¹ * γ₀ * h))
    (Ψ : GL (Fin 2) F → Set (AdelicGL2 (𝓞 F) F))
    (hΨs : ∀ γ₀ ∈ R, Ψ γ₀ ⊆
      {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΨ : ∀ γ₀ ∈ R, IsFundamentalDomain
      ((Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) F))).map (AutomorphicForm.globalPoints (𝓞 F) F)) (Ψ γ₀)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    (∫ x in Φ, (∫ z in Ω, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (AutomorphicForm.adelicKernelCentralPart F f x (AutomorphicForm.centralScalar (𝓞 F) F z * x) +
          AutomorphicForm.adelicKernelEllipticPart F f x (AutomorphicForm.centralScalar (𝓞 F) F z * x)) ∂νZ)
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) =
    ∑ᶠ γ₀ ∈ R,
      ((Nat.card {a : Fˣ // ∃ h : GL (Fin 2) F,
          Matrix.GeneralLinearGroup.scalar (Fin 2) a * γ₀ = h⁻¹ * γ₀ * h} : ℕ) : ℂ)⁻¹ *
        ∫ z : (AdeleRing (𝓞 F) F)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (∫ x in Ψ γ₀, f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ₀ *
            (AutomorphicForm.centralScalar (𝓞 F) F z * x)) ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) ∂νZ := by sorry
