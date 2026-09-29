-- Prove2me | Theorems.Thm_AutomorphicForm_isFundamentalDomain_image_and_forall_setLIntegral_indicator_slab_bracket_eq_of_lintegral_eq
-- name    : AutomorphicForm.isFundamentalDomain_image_and_forall_setLIntegral_indicator_slab_bracket_eq_of_lintegral_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/27c69810-dda8-5ef5-bfca-6cf21611b22b
-- title:
--   Slab-cut truncated shell integrals on a twisted diagonal centraliser
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ Galois, and let $0 < \alpha < \beta$ be reals. Fix a Haar measure $\nu_{Z_L}$ on $(\mathbb{A}_L)^\times$ and a set $\Omega_L$ that is a fundamental domain for the subgroup of principal ideles (the range of $L^\times \to (\mathbb{A}_L)^\times$) acting on $(\mathbb{A}_L)^\times$, and a Haar measure $\nu_K$ on $(\mathbb{A}_K)^\times$ with fundamental domain $\Omega_K$ for the principal ideles of $K$. Let $D$ be a datum [`M4aHerbrand.IdeleGaloisDescent`](def/M4aHerbrand_IdeleClassVocab.html#L28) for $L/K$, i.e. a homomorphism from $\mathrm{Gal}(L/K)$ to the continuous ring automorphisms of $\mathbb{A}_L$ compatible with $L \to \mathbb{A}_L$, and let $\sigma$ generate $\mathrm{Gal}(L/K)$ in the sense that every $\tau$ lies in the subgroup of integral powers of $\sigma$. Let $H$ be a closed subgroup of $\mathrm{GL}_2(\mathbb{A}_L)$ consisting exactly of those $h$ whose off-diagonal entries $h_{10}$ and $h_{01}$ vanish and for which $\sigma$ acting entrywise through $D$ on $h$, times $h^{-1}$, is central; let $\mu_H$ be a Haar measure on $H$ that is also right invariant. Let $\Lambda_0 \le \mathrm{GL}_2(L)$ consist exactly of the diagonal matrices $\gamma$ with $\gamma_{00}/\gamma_{11}$ in the image of $K$ in $L$. Let $\theta\colon (\mathbb{A}_K)^\times \to (\mathbb{A}_L)^\times$ be a continuous injective homomorphism with $\|\theta a\|_L = \|a\|_K^{[L:K]}$ (norms being the module of the translation action on additive Haar measure) and $\theta$ compatible with principal ideles via $K \to L$; and let $c_H > 0$ satisfy $\int^- _H f(h)\,d\mu_H = c_H \iint f(z \cdot \mathrm{diag}(\theta a,1))\,d\nu_K\,d\nu_{Z_L}$, for every measurable $f \colon \mathrm{GL}_2(\mathbb{A}_L) \to [0,\infty]$, where $z$ denotes the central scalar matrix. Write $\kappa_0 = c_H \cdot \nu_{Z_L}(\Omega_L \cap \{\|z\|_L \in [1,e]\}) \cdot \nu_K(\Omega_K \cap \{\|a\|_K \in [1,e]\}) \cdot \log(\beta/\alpha) / (2[L:K])$ (measures read as reals), let $w$ be the image in $\mathrm{GL}_2(\mathbb{A}_L)$ of the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ over $L$, and let $\mathrm{H}(\cdot)$ be the adelic height, the product of the archimedean and finite local heights. Then: (a) $\{h \in H : h = z \cdot \mathrm{diag}(\theta a,1)$ for some $z \in \Omega_L$, $a \in \Omega_K\}$ is a fundamental domain in $H$, with respect to $\mu_H$, for the subgroup of $H$ induced by the image of $\Lambda_0$ in $\mathrm{GL}_2(\mathbb{A}_L)$; and (b) for every $\mu_H$-fundamental domain $\Omega \subseteq H$ for that same subgroup, every $y \in \mathrm{GL}_2(\mathbb{A}_L)$ and every real $R$, the integrand $h \mapsto \mathbf{1}_{\{\|\det g\|_L \in [\alpha,\beta]\}}(hy)\bigl(1 - \mathbf{1}_{\{e^R < \mathrm{H}(y')\}}(hy) - \mathbf{1}_{\{e^R < \mathrm{H}(w y')\}}(hy)\bigr)$, with values in $\mathbb{C}$, has extended-norm integral over $\Omega$ equal to $\kappa_0\,|2R - \log \mathrm{H}(y) - \log \mathrm{H}(wy)|$, and, provided $\mathrm{H}(y)\,\mathrm{H}(wy) \le e^{2R}$, it is integrable on $\Omega$ with $\int_\Omega = \kappa_0\,(2R - \log \mathrm{H}(y) - \log \mathrm{H}(wy))$ viewed in $\mathbb{C}$.
--
--   This is the torus-shell evaluation for the $\sigma$-twisted trace formula of $\mathrm{GL}_2$ over a cyclic extension $L/K$: the truncated, determinant-slab-cut orbital integrand over the twisted diagonal centraliser is computed in idelic coordinates, with an explicit constant and for an arbitrary fundamental domain of the rational diagonal lattice $\Lambda_0$. It is the shared core of the existence statement [`AutomorphicForm.exists_pos_isFundamentalDomain_forall_setIntegral_indicator_slab_bracket_eq_mul_of_sigmaCentraliser`](thm.html#AutomorphicForm.exists_pos_isFundamentalDomain_forall_setIntegral_indicator_slab_bracket_eq_mul_of_sigmaCentraliser) and of the uniqueness statement [`AutomorphicForm.torusShell_const_eq_of_forall_lintegral_eq`](thm.html#AutomorphicForm.torusShell_const_eq_of_forall_lintegral_eq) for the constant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isFundamentalDomain_image_and_forall_setLIntegral_indicator_slab_bracket_eq_of_lintegral_eq.lean

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

theorem AutomorphicForm.isFundamentalDomain_image_and_forall_setLIntegral_indicator_slab_bracket_eq_of_lintegral_eq
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
        ENNReal.ofReal cH * ∫⁻ z, ∫⁻ a, f (AutomorphicForm.centralScalar (𝓞 L) L z * diagOne (θ a)) ∂νK ∂νZL) :
    IsFundamentalDomain ((Λ₀.map (AutomorphicForm.globalPoints (𝓞 L) L)).subgroupOf H)
      {h : H | ∃ z ∈ ΩL, ∃ a ∈ ΩK,
        (h : AdelicGL2 (𝓞 L) L) = AutomorphicForm.centralScalar (𝓞 L) L z * diagOne (θ a)} μH ∧
    ∀ (Ω : Set H), IsFundamentalDomain ((Λ₀.map (AutomorphicForm.globalPoints (𝓞 L) L)).subgroupOf H) Ω μH →
      ∀ (y : AdelicGL2 (𝓞 L) L) (R : ℝ),
        (∫⁻ h in Ω, ‖Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y))‖ₑ ∂μH =
          ENNReal.ofReal ((cH * (νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc 1 (Real.exp 1)})).toReal *
      (νK (ΩK ∩ {a | NumberField.TateGlobal.ideleNorm K a ∈ Set.Icc 1 (Real.exp 1)})).toReal *
      Real.log (β / α) / (2 * Module.finrank K L)) * |(2 * R - Real.log (NumberField.AdelicHeight.adelicHeight L y)
            - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)))|)) ∧
        (NumberField.AdelicHeight.adelicHeight L y *
            NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y) ≤ Real.exp (2 * R) →
          IntegrableOn (fun h : H => Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y) *
            ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y))) Ω μH ∧
          ∫ h in Ω, Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y) *
            ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y)) ∂μH =
            (((cH * (νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L z ∈ Set.Icc 1 (Real.exp 1)})).toReal *
      (νK (ΩK ∩ {a | NumberField.TateGlobal.ideleNorm K a ∈ Set.Icc 1 (Real.exp 1)})).toReal *
      Real.log (β / α) / (2 * Module.finrank K L)) * (2 * R - Real.log (NumberField.AdelicHeight.adelicHeight L y)
            - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y))) : ℝ) : ℂ)) := by sorry
