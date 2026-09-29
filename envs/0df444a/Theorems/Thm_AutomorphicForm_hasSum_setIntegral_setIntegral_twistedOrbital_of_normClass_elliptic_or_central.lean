-- Prove2me | Theorems.Thm_AutomorphicForm_hasSum_setIntegral_setIntegral_twistedOrbital_of_normClass_elliptic_or_central
-- name    : AutomorphicForm.hasSum_setIntegral_setIntegral_twistedOrbital_of_normClass_elliptic_or_central
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/020c9bc0-2015-51c0-bf92-5cd01e7f792a
-- title:
--   Twisted orbital expansion of the elliptic and central kernel part
-- statement:
--   Let $L/K$ be an extension of number fields that is finite and Galois, and let $\sigma \in \mathrm{Gal}(L/K)$ be such that every $\tau$ lies in the subgroup of integer powers of $\sigma$. Let $D$ be a Galois descent datum for the adeles, i.e. a monoid homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$ which is continuous in each element and agrees with the Galois action on principal adeles; write $\sigma_{\mathbb{A}}$ for the induced entrywise automorphism of $\mathrm{GL}_2(\mathbb{A}_L)$, $\iota$ for the map $\mathrm{GL}_2(L) \to \mathrm{GL}_2(\mathbb{A}_L)$ on global points, and $\underline{z}$ for the scalar matrix attached to an idele $z$. Fix $\alpha, \beta \in \mathbb{R}$ and let $X$ be the slab of $g$ with $\|\det g\| \in [\alpha,\beta]$, where $\|x\|$ is the value of the distributive Haar character of $\mathbb{A}_L$ at $x$; let $dg$ be the Haar measure of $\mathrm{GL}_2(\mathbb{A}_L)$ for its Borel structure, and let $\Phi \subseteq X$ be a fundamental domain for $\iota(\mathrm{GL}_2(L))$ acting on $\mathrm{GL}_2(\mathbb{A}_L)$ with respect to $dg|_X$. Let $\nu_Z$ be a Haar measure on the idele group $\mathbb{A}_L^\times$ (with a Borel measurable structure), $\Omega \subseteq \mathbb{A}_L^\times$ a set, and $\xi$ a homomorphism from the full subgroup of $\mathbb{A}_L^\times$ to $\mathbb{C}^\times$ whose associated function $z \mapsto \xi(z)$ into $\mathbb{C}$ is continuous. Let $\mathrm{rep}$ assign to each $\sigma$-conjugacy class in $\mathrm{GL}_2(L)$ an element of that class, and for each class $c$ whose norm class $N(c) \in \mathrm{ConjClasses}(\mathrm{GL}_2(K))$ is the conjugacy class of some $\gamma \in \mathrm{GL}_2(K)$ which is either elliptic (the characteristic polynomial of $\gamma$ has no root in $K$) or central (a scalar matrix), let $\Psi(c)$ be a fundamental domain, with respect to $dg|_X$, for the image under $\iota$ of the $\sigma$-twisted centraliser $\{t \in \mathrm{GL}_2(L) : t\,\mathrm{rep}(c)\,\sigma(t)^{-1} = \mathrm{rep}(c)\}$, with $\sigma$ acting entrywise. Let $\varphi$ be a continuous, compactly supported complex function on $\mathrm{GL}_2(\mathbb{A}_L)$, and assume the absolute convergence hypothesis that the iterated lower integral over $x \in \Phi$ and $z \in \Omega$ of $\sum_{\delta} \|\xi(z)\,\varphi(x^{-1} \iota(\delta)\,\sigma_{\mathbb{A}}(\underline{z}x))\|$ is finite, the sum being over those $\delta \in \mathrm{GL}_2(L)$ whose $\sigma$-conjugacy class has elliptic or central norm class. The conclusion is that the family indexed by the $\sigma$-conjugacy classes $c$ with elliptic or central norm class, whose $c$-th term is $$\int_{\Psi(c)} \int_{\Omega} \xi(z)\,\varphi\bigl(x^{-1} \iota(\mathrm{rep}(c))\,\sigma_{\mathbb{A}}(\underline{z}x)\bigr)\,d\nu_Z(z)\,dg|_X(x),$$ is summable with sum $$\int_{\Phi} \int_{\Omega} \xi(z) \sum_{\delta} \varphi\bigl(x^{-1}\iota(\delta)\,\sigma_{\mathbb{A}}(\underline{z}x)\bigr)\,d\nu_Z(z)\,dg(x),$$ the inner sum being the finite-support sum over the same set of $\delta$.
--
--   This is the class-by-class expansion of the elliptic and central-norm part of the $\sigma$-twisted $\mathrm{GL}_2$ kernel, folded over the centre and integrated over a determinant slab quotient: the terms (10.8)–(10.9) of Langlands' twisted trace formula for $\mathrm{GL}(2)$. It is used to rewrite the fold of the twisted kernel as a sum of twisted orbital integrals over the twisted centralisers, in the form required for the comparison with the trace formula over $K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_hasSum_setIntegral_setIntegral_twistedOrbital_of_normClass_elliptic_or_central.lean

import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_TwistedNormClasses
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.hasSum_setIntegral_setIntegral_twistedOrbital_of_normClass_elliptic_or_central
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (α β : ℝ) (Φ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (hΦs : Φ ⊆
      {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 L) L).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZ : Measure (AdeleRing (𝓞 L) L)ˣ) [νZ.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 L) L)ˣ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (rep : LT.TwistedNorm.SigmaConjClasses σ → GL (Fin 2) L)
    (hrep : ∀ c, LT.TwistedNorm.SigmaConjClasses.mk σ (rep c) = c)
    (Ψ : LT.TwistedNorm.SigmaConjClasses σ → Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (hΨ : ∀ c : LT.TwistedNorm.SigmaConjClasses σ,
      (∃ γ : GL (Fin 2) K, (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen c = ConjClasses.mk γ) →
      IsFundamentalDomain
        ((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (rep c)).map
          (AutomorphicForm.globalPoints (𝓞 L) L)) (Ψ c)
        ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
          {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (habs : ∫⁻ x in Φ, ∫⁻ z in Ω,
        ∑' δ : {δ : GL (Fin 2) L // ∃ γ : GL (Fin 2) K,
            (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) =
              ConjClasses.mk γ},
          ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))‖ₑ
          ∂νZ ∂(adelicGLHaar (Fin 2) (𝓞 L) L) < ⊤) :
    HasSum
      (fun c : {c : LT.TwistedNorm.SigmaConjClasses σ // ∃ γ : GL (Fin 2) K,
          (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
          LT.TwistedNorm.normClassMap hgen c = ConjClasses.mk γ} =>
        ∫ x in Ψ c, (∫ z in Ω, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L (rep c) *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZ)
          ∂((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
            {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
      (∫ x in Φ, (∫ z in Ω, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          (∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
              (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
              LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) =
                ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ∂νZ)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) := by sorry
