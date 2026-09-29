-- Prove2me | Theorems.Thm_AutomorphicForm_torusShell_const_eq_of_forall_lintegral_eq
-- name    : AutomorphicForm.torusShell_const_eq_of_forall_lintegral_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/ebffc153-313f-5337-bd2c-c45f8a579920
-- title:
--   The torus-shell constant κ₀ evaluated
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ Galois, and let $\alpha, \beta$ be reals with $0 < \alpha < \beta$. Fix a Haar measure $\nu_{ZL}$ on $(\mathbb{A}_L)^\times$ (for the Borel structure) and a set $\Omega_L$ that is a fundamental domain for the action of the image of $L^\times$ under the principal-idele map, and likewise a Haar measure $\nu_K$ on $(\mathbb{A}_K)^\times$ with fundamental domain $\Omega_K$ for the image of $K^\times$. Let $D$ be an [`M4aHerbrand.IdeleGaloisDescent`](def/M4aHerbrand_IdeleClassVocab.html#L28), i.e. a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$ which is continuous in each member and compatible with the principal-adele map, and let $\sigma$ be such that every element of $\mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$. Let $H$ be a closed subgroup of $\mathrm{GL}_2(\mathbb{A}_L)$ whose elements $h$ are exactly those with both off-diagonal entries zero and with $D(\sigma)(h) h^{-1}$ central, carrying a Haar measure $\mu_H$ that is moreover right invariant; let $\Lambda_0 \le \mathrm{GL}_2(L)$ consist exactly of the diagonal $\gamma$ with $\gamma_{00}/\gamma_{11} \in K$. Let $\theta : (\mathbb{A}_K)^\times \to (\mathbb{A}_L)^\times$ be a continuous injective homomorphism with $\|\theta a\|_L = \|a\|_K^{[L:K]}$ (idele norms being the moduli of the distributive Haar characters) which carries principal ideles of $K$ to principal ideles of $L$, and let $c_H > 0$ be a constant with $\int_H f \, d\mu_H = c_H \int \int f(z \cdot \mathrm{diag}(\theta a, 1)) \, d\nu_K(a) \, d\nu_{ZL}(z)$ for every measurable $f : \mathrm{GL}_2(\mathbb{A}_L) \to [0,\infty]$, where $z$ denotes the central scalar matrix. Finally let $\kappa_0 \in \mathbb{R}$ and let $\Omega \subseteq H$ be a fundamental domain, in $H$, for the image of $\Lambda_0$ in $\mathrm{GL}_2(\mathbb{A}_L)$, such that for all $y \in \mathrm{GL}_2(\mathbb{A}_L)$ and all $R \in \mathbb{R}$ the integral over $\Omega$ against $\mu_H$ of the extended norm of the indicator of the slab $\{g : \|\det g\|_L \in [\alpha,\beta]\}$ at $hy$, multiplied by $1 - \mathbf{1}[e^R < \mathrm{H}_L(hy)] - \mathbf{1}[e^R < \mathrm{H}_L(w \cdot hy)]$ with $\mathrm{H}_L$ the adelic height and $w$ the image in $\mathrm{GL}_2(\mathbb{A}_L)$ of the antidiagonal matrix $\begin{pmatrix} 0&1\\1&0\end{pmatrix}$, equals $\kappa_0 \, |2R - \log \mathrm{H}_L(y) - \log \mathrm{H}_L(wy)|$ as an element of $[0,\infty]$. Then $$\kappa_0 = c_H \cdot \nu_{ZL}\big(\Omega_L \cap \{\|z\|_L \in [1,e]\}\big) \cdot \nu_K\big(\Omega_K \cap \{\|a\|_K \in [1,e]\}\big) \cdot \frac{\log(\beta/\alpha)}{2[L:K]},$$ the two measures being read as real numbers.
--
--   This pins down, in the normalisation fixed by $\mu_H$, $\nu_{ZL}$ and $\nu_K$, the proportionality constant in the weighted (hyperbolic) term attached to the $\sigma$-twisted centraliser of the diagonal torus of $\mathrm{GL}_2$ over a cyclic extension $L/K$, so that constants computed on the $L$-side and on the $K$-side can be compared in a single measure normalisation. It feeds the comparison of hyperbolic intercepts with Satake data in the twisted trace identity for $\mathrm{GL}_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_torusShell_const_eq_of_forall_lintegral_eq.lean

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
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.torusShell_const_eq_of_forall_lintegral_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (Λ₀ : Subgroup (GL (Fin 2) L))
    (hΛ₀ : ∀ γ : GL (Fin 2) L, γ ∈ Λ₀ ↔ (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L))

    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νK)
    (θ : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 L) L)ˣ) (hθ : Continuous θ) (hθi : Function.Injective θ)
    (hθn : ∀ a, NumberField.TateGlobal.ideleNorm L (θ a) = NumberField.TateGlobal.ideleNorm K a ^ Module.finrank K L)
    (hθc : ∀ k : Kˣ, θ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k) =
      Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) (Units.map (algebraMap K L : K →* L) k))
    (cH : ℝ) (hcH : 0 < cH)
    (hμH : ∀ f : AdelicGL2 (𝓞 L) L → ENNReal, Measurable f →
      ∫⁻ h : H, f (h : AdelicGL2 (𝓞 L) L) ∂μH =
        ENNReal.ofReal cH * ∫⁻ z, ∫⁻ a, f (AutomorphicForm.centralScalar (𝓞 L) L z * diagOne (θ a)) ∂νK ∂νZL)
    (κ₀ : ℝ) (Ω : Set H)
    (hΩ : IsFundamentalDomain ((Λ₀.map (AutomorphicForm.globalPoints (𝓞 L) L)).subgroupOf H) Ω μH)
    (hκ₀ : ∀ (y : AdelicGL2 (𝓞 L) L) (R : ℝ),
      ∫⁻ h in Ω, ‖Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y))‖ₑ ∂μH =
        ENNReal.ofReal (κ₀ * |2 * R - Real.log (NumberField.AdelicHeight.adelicHeight L y)
          - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y))|)) :
    κ₀ = cH * (νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc 1 (Real.exp 1)})).toReal *
      (νK (ΩK ∩ {a | NumberField.TateGlobal.ideleNorm K a ∈ Set.Icc 1 (Real.exp 1)})).toReal *
      Real.log (β / α) / (2 * Module.finrank K L) := by sorry
