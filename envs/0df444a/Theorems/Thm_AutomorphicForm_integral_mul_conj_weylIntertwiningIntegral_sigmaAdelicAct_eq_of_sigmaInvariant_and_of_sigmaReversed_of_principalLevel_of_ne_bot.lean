-- Prove2me | Theorems.Thm_AutomorphicForm_integral_mul_conj_weylIntertwiningIntegral_sigmaAdelicAct_eq_of_sigmaInvariant_and_of_sigmaReversed_of_principalLevel_of_ne_bot
-- name    : AutomorphicForm.integral_mul_conj_weylIntertwiningIntegral_sigmaAdelicAct_eq_of_sigmaInvariant_and_of_sigmaReversed_of_principalLevel_of_ne_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/27a318bf-fa8c-5f74-b343-cd96a9e37203
-- title:
--   Adjointness of the Weyl intertwining integral under a Galois twist
-- statement:
--   Let $K \subseteq L$ be number fields, $D$ an idele Galois descent datum for $L/K$ (a homomorphism from $\mathrm{Aut}_K(L)$ to ring automorphisms of $\mathbb{A}_L$, continuous and compatible with $L \to \mathbb{A}_L$), $\sigma \in \mathrm{Aut}_K(L)$ and $N \neq 0$ an ideal of $\mathcal{O}_L$. Write $\alpha_m$ for the positive real character of $\mathbb{A}_L^{\times}$ obtained from `distribHaarChar`, and $|z|^{s} := \alpha_m(z)^{s}$ via `cpowChar`. Let $\mu,\nu : \mathbb{A}_L^{\times} \to \mathbb{C}^{\times}$ be continuous characters that are unitary ($|\chi(x)| = 1$) and trivial on the principal ideles $L^{\times}$. Let $(\varphi_s)_{s \in \mathbb{C}}$ and $(\psi_s)_{s \in \mathbb{C}}$ be families of functions on $\mathrm{GL}_2(\mathbb{A}_L)$ such that each $\varphi_s$, $\psi_s$ is a section induced from $(\mu|\cdot|^{s+1/2}, \nu|\cdot|^{-(s+1/2)})$, i.e. transforms under the adelic Borel by the product of those characters on the two diagonal entries, is $K_\infty$-finite at every infinite place (finitely many right translates under each row-isometry subgroup span), is $K_f$-smooth (open stabiliser inside $\ker(\mathrm{gl}_{\mathrm{arch}})$) and is right invariant under $\mathrm{principalLevel}(N) \sqcap \mathrm{finiteAdelicGL2Subgroup}$; jointly continuous in $(s,g)$, holomorphic in $s$, uniformly $K_\infty$-finite (one finite-dimensional space of functions on each row-isometry subgroup for all $s$ and $g$), and flat ($\varphi_s(k) = \varphi_0(k)$ on the adelic maximal compact, likewise for $\psi$). Let $O_\varphi$ be open and preconnected containing $\{\mathrm{Re}\,s = 0\}$ and $\{\mathrm{Re}\,s > 1/2\}$, and $E_\varphi, N_\varphi$ functions analytic in $s$ on $O_\varphi$, continuous on $O_\varphi \times \mathrm{GL}_2(\mathbb{A}_L)$, agreeing for $\mathrm{Re}\,s > 1/2$ with the Eisenstein sum $\varphi_s(g) + \sum_{\xi \in L} \varphi_s(w\,u(\xi)\,g)$ and with the Weyl intertwining integral $\int_{\mathbb{A}_L} \varphi_s(w^{-1}u(x)g)\,dx$ for the adelic additive Haar measure; similarly $O_\psi, E_\psi, N_\psi$ for $\psi$. Set $M_s := \mathrm{vol}(\mathrm{adelicBox})^{-1} N_s$ and let $\sigma$ act on $\mathrm{GL}_2(\mathbb{A}_L)$ entrywise through $D.\mathrm{act}\,\sigma^{-1}$. The conclusion is the conjunction of two assertions about the point $s = -i\theta/2$ on the unitary axis. First, if $\mu$ and $\nu$ are invariant under the induced action of $\sigma^{-1}$ on ideles and $\mu = \nu|\cdot|^{i\theta}$ for a real $\theta$, then $\int_{\mathbf{K}} \varphi_{-i\theta/2}(k)\,\overline{(M_{-i\theta/2}\psi)(\sigma^{-1}k)}\,dk = \int_{\mathbf{K}} (M_{-i\theta/2}\varphi)(k)\,\overline{\psi_{-i\theta/2}(\sigma^{-1}k)}\,dk$, the integrals being over the adelic maximal compact with its Haar measure. Second, for every real $\tau$, if $\mu \circ \sigma^{-1} = \nu|\cdot|^{i\tau}$ and $\nu \circ \sigma^{-1} = \mu|\cdot|^{-i\tau}$ while at least one of $\mu, \nu$ fails to be $\sigma^{-1}$-invariant, then the same identity holds at $s = -i\tau/2$.
--
--   This is the adjointness (unitarity) relation for the Weyl intertwining operator on the unitary axis, transported across the Galois twist $g \mapsto \sigma^{-1}(g)$, in the two character configurations that occur for a $\sigma$-twisted pair: the diagonal case, where the pair is $\sigma$-invariant and $\mu$ and $\nu$ differ by an unramified unitary twist, and the swapped case, where $\sigma$ interchanges the two characters up to such a twist. It supplies the cancellation of the twisted cross terms in the continuous part of the twisted trace formula, and is used in the construction of the limiting atomic measure attached to a semi-local factorisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integral_mul_conj_weylIntertwiningIntegral_sigmaAdelicAct_eq_of_sigmaInvariant_and_of_sigmaReversed_of_principalLevel_of_ne_bot.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.integral_mul_conj_weylIntertwiningIntegral_sigmaAdelicAct_eq_of_sigmaInvariant_and_of_sigmaReversed_of_principalLevel_of_ne_bot
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (N : Ideal (𝓞 L)) (_hN : N ≠ ⊥) :
    let αm : (AdeleRing (𝓞 L) L)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 L) L))).toHomUnits
    letI := adeleBorel (𝓞 L) L
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 L) L μ) (_hν : IsUnitaryChar (𝓞 L) L ν)
      (_hμF : IsIdeleClassChar (𝓞 L) L μ) (_hνF : IsIdeleClassChar (𝓞 L) L ν)
      (_hμk : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((ν x : ℂˣ) : ℂ))
      (φf : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hφf : ∀ s, IsInducedSection (𝓞 L) L (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φf s))
      (_hφfK : ∀ s, IsArchKFinite L (φf s))
      (_hφff : ∀ s, IsKfSmooth L (φf s))
      (_hφfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 L) L => φf p.1 p.2))
      (_hφfhol : ∀ g, Differentiable ℂ (fun s => φf s g))
      (_hφfKu : ∀ w : InfinitePlace L, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup L w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
          (fun k : ↥(archRowIsometrySubgroup L w) => φf s (g * (k : AdelicGL2 (𝓞 L) L))) ∈ W)
      (_hφflat : ∀ (s : ℂ) (k : adelicMaximalCompact L),
        φf s (k : AdelicGL2 (𝓞 L) L) = φf 0 (k : AdelicGL2 (𝓞 L) L))
      (_hφflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
        ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, φf s (g * u) = φf s g)
      (ψf : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 L) L (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite L (ψf s))
      (_hψff : ∀ s, IsKfSmooth L (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 L) L => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ w : InfinitePlace L, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup L w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
          (fun k : ↥(archRowIsometrySubgroup L w) => ψf s (g * (k : AdelicGL2 (𝓞 L) L))) ∈ W)
      (_hψflat : ∀ (s : ℂ) (k : adelicMaximalCompact L),
        ψf s (k : AdelicGL2 (𝓞 L) L) = ψf 0 (k : AdelicGL2 (𝓞 L) L))
      (_hψflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
        ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, ψf s (g * u) = ψf s g)
      (Oφ : Set ℂ) (Eφ Nφ : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hEφ :
      IsOpen Oφ ∧ IsPreconnected Oφ ∧ {s : ℂ | s.re = 0} ⊆ Oφ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oφ ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Eφ s g) Oφ) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Nφ s g) Oφ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Eφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Nφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        Eφ s g = φf s g + ∑' ξ : L, φf s (adelicWeyl (𝓞 L) L
          * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        Nφ s g = weylIntertwiningIntegral (𝓞 L) L (adelicAddHaar (𝓞 L) L) (φf s) g))
      (Oψ : Set ℂ) (Eψ Nψ : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hEψ :
      IsOpen Oψ ∧ IsPreconnected Oψ ∧ {s : ℂ | s.re = 0} ⊆ Oψ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oψ ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Eψ s g) Oψ) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Nψ s g) Oψ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Eψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Nψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        Eψ s g = ψf s g + ∑' ξ : L, ψf s (adelicWeyl (𝓞 L) L
          * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        Nψ s g = weylIntertwiningIntegral (𝓞 L) L (adelicAddHaar (𝓞 L) L) (ψf s) g)),
      ((∀ z : (AdeleRing (𝓞 L) L)ˣ, μ (D.unitsAct σ.symm z) = μ z) → (∀ z : (AdeleRing (𝓞 L) L)ˣ, ν (D.unitsAct σ.symm z) = ν z) →
        ∀ θ : ℝ, (∀ z : (AdeleRing (𝓞 L) L)ˣ, μ z = ν z * cpowChar αm hαm ((θ : ℂ) * Complex.I) z) →
        (∫ k, φf (((-(θ / 2) : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L) * conj ((fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nψ (((-(θ / 2) : ℝ) : ℂ) * Complex.I) g) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L)) =
        (∫ k, (fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nφ (((-(θ / 2) : ℝ) : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L) * conj (ψf (((-(θ / 2) : ℝ) : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L))) ∧
      (∀ τ : ℝ, (∀ z : (AdeleRing (𝓞 L) L)ˣ, μ (D.unitsAct σ.symm z) = ν z * cpowChar αm hαm ((τ : ℂ) * Complex.I) z) →
        (∀ z : (AdeleRing (𝓞 L) L)ˣ, ν (D.unitsAct σ.symm z) = μ z * cpowChar αm hαm (-((τ : ℂ) * Complex.I)) z) →
        (∃ z : (AdeleRing (𝓞 L) L)ˣ, μ (D.unitsAct σ.symm z) ≠ μ z ∨ ν (D.unitsAct σ.symm z) ≠ ν z) →
        (∫ k, φf (((-(τ / 2) : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L) * conj ((fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nψ (((-(τ / 2) : ℝ) : ℂ) * Complex.I) g) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L)) =
        (∫ k, (fun g => ((((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ))⁻¹ * Nφ (((-(τ / 2) : ℝ) : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 L) L) * conj (ψf (((-(τ / 2) : ℝ) : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm (k : AdelicGL2 (𝓞 L) L))) ∂(AutomorphicForm.maximalCompactHaar L))) := by sorry
