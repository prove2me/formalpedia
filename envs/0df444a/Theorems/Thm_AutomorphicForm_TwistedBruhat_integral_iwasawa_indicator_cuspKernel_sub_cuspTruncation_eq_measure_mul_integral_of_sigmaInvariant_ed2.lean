-- Prove2me | Theorems.Thm_AutomorphicForm_TwistedBruhat_integral_iwasawa_indicator_cuspKernel_sub_cuspTruncation_eq_measure_mul_integral_of_sigmaInvariant_ed2
-- name    : AutomorphicForm.TwistedBruhat.integral_iwasawa_indicator_cuspKernel_sub_cuspTruncation_eq_measure_mul_integral_of_sigmaInvariant_ed2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/1fbbb132-683a-5afd-8101-e49431265177
-- title:
--   Centre removal in the Iwasawa integral of the twisted cusp kernel
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ Galois, let $0 < \alpha \le \beta$ be reals, let $\nu_{Z_L}$ be a Haar measure on the idele group $(\mathbb{A}_L)^\times$ (with its Borel structure) and let $\Omega_L$ be a fundamental domain for the image of $L^\times$ under `Units.map (algebraMap L (AdeleRing (𝓞 L) L))` acting on $(\mathbb{A}_L)^\times$ for $\nu_{Z_L}$. Let $D$ be a descent datum, i.e. a monoid homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$ which is continuous and extends the Galois action on $L$, and let $\sigma$ be an element of $\mathrm{Gal}(L/K)$ all of whose conjugates — indeed all Galois elements — lie in $\langle \sigma \rangle$. Let $\xi_L$ be a homomorphism from the full idele group (as the top subgroup) to $\mathbb{C}^\times$ which is continuous as a $\mathbb{C}$-valued function, trivial on principal ideles, and invariant under the automorphism of $(\mathbb{A}_L)^\times$ induced by $D$ at $\sigma$. Let $\varphi : GL_2(\mathbb{A}_L) \to \mathbb{C}$ be continuous with compact support, $R$ real, $X$ a set of adeles, and $\Omega_1, \Omega_2$ sets of ideles with $\Omega_1$ a fundamental domain for the principal ideles with respect to `idelicHaar`. Write $Z(g) = \int_{\Omega_L} \xi_L(z)\bigl(\mathrm{cuspKernel}(z,g) - \mathrm{cuspTruncation}(z,g)\bigr)\, d\nu_{Z_L}(z)$, where the cusp kernel at $(z,g)$ is the unordered sum of $\varphi\bigl(g^{-1}\,\beta_{\mathbb{A}}\, \sigma\text{-twisted-translate of } z g\bigr)$ over the rational points $\beta$ lying in the intersection of `normUnipotentSet` with the Borel subgroup of $GL_2(L)$, and the truncation at $(z,g)$ is the indicator of the set where the adelic height exceeds $e^R$, evaluated at the central translate $z g$, applied to the constant term along the unipotent one-parameter subgroup (for the adelic Haar measure conditioned on the adelic box) of the sum of $\varphi(g^{-1}\delta_{\mathbb{A}} \,\sigma\text{-twisted-translate})$ over $\delta$ in `borelNormOneSet`. Assume that the iterated lower integral of the enorm of the integrand below, over $x \in X$ for the adelic additive Haar measure, $u \in \Omega_1$ and $t \in \Omega_2$ for `idelicHaar`, and $k$ over the Haar measure of the subgroup `adelicMaximalCompact` (elements integral at the finite places and acting by row isometries at the infinite places), is finite. Then $$\int_X \int_{\Omega_1} \int_{\Omega_2} \int_{\mathbf{K}} \mathbf{1}_{\{|\det| \in [\alpha,\beta]\}}\bigl(n(x)\,z(u)\,\mathrm{diag}(t,1)\,k\bigr)\,Z\bigl(n(x)z(u)\mathrm{diag}(t,1)k\bigr)\,|t|^{-1} = \mathrm{vol}\bigl(\Omega_1 \cap \{u : |u|^2 \in [\alpha,\beta]\}\bigr)\cdot \int_X \int_{\Omega_2}\int_{\mathbf{K}} Z\bigl(n(x)\mathrm{diag}(t,1)k\bigr)\,|t|^{-1},$$ where $n(x)$ is the upper unipotent matrix with entry $x$, $z(u)$ the central scalar $u$, $|\cdot|$ is the idele norm given by the distributive Haar character, and the volume is taken for `idelicHaar` and converted to a real number and then to $\mathbb{C}$.
--
--   This is the step in the Iwasawa-coordinate evaluation of the unipotent-type contribution to the $\sigma$-twisted trace formula for $GL_2$ over $L$ at which the central variable is integrated out: by $\sigma$-invariance of the central character the inner kernel is unchanged by central translation, so the central integral contributes only the volume of a norm shell. It feeds the rank-one reduction statement [`AutomorphicForm.exists_forall_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_sum_mul_setIntegral_rankOne_of_sigmaInvariant_unram_ed2`](thm.html#AutomorphicForm.exists_forall_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_sum_mul_setIntegral_rankOne_of_sigmaInvariant_unram_ed2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_TwistedBruhat_integral_iwasawa_indicator_cuspKernel_sub_cuspTruncation_eq_measure_mul_integral_of_sigmaInvariant_ed2.lean

import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.TwistedBruhat.integral_iwasawa_indicator_cuspKernel_sub_cuspTruncation_eq_measure_mul_integral_of_sigmaInvariant_ed2
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξσ : ∀ z₀ : (AdeleRing (𝓞 L) L)ˣ,
      ξL ⟨M4aHerbrand.IdeleGaloisDescent.unitsAct D σ z₀, Subgroup.mem_top _⟩ = ξL ⟨z₀, Subgroup.mem_top z₀⟩)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) (R : ℝ)
    (X : Set (AdeleRing (𝓞 L) L)) (Ω₁ Ω₂ : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩ₁ : @IsFundamentalDomain (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range _ _ _
      (NumberField.Idele.ideleBorel L) Ω₁ (NumberField.Idele.idelicHaar L))
    (hfin : ∫⁻ x in X, ∫⁻ u in Ω₁, ∫⁻ t in Ω₂, ∫⁻ k,
            ‖Set.indicator
              ({g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} :
                Set (AdelicGL2 (𝓞 L) L))
              (fun g : AdelicGL2 (𝓞 L) L => ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                (TwistedBruhat.cuspKernel K L D σ hgen φ z g - TwistedBruhat.cuspTruncation K L D σ R φ z g) ∂νZL)
              (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
              (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)‖ₑ
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) ≠ ⊤) :
    (∫ x in X, ∫ u in Ω₁, ∫ t in Ω₂, ∫ k,
            Set.indicator
              ({g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} :
                Set (AdelicGL2 (𝓞 L) L))
              (fun g : AdelicGL2 (𝓞 L) L => ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                (TwistedBruhat.cuspKernel K L D σ hgen φ z g - TwistedBruhat.cuspTruncation K L D σ R φ z g) ∂νZL)
              (unipotentGL2 x * centralScalar (𝓞 L) L u * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
              (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L)) =
      ((NumberField.Idele.idelicHaar L
          (Ω₁ ∩ {u | NumberField.TateGlobal.ideleNorm L u ^ 2 ∈ Set.Icc α β})).toReal : ℂ) *
      (∫ x in X, ∫ t in Ω₂, ∫ k,
            (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                (TwistedBruhat.cuspKernel K L D σ hgen φ z (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)) - TwistedBruhat.cuspTruncation K L D σ R φ z (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))) ∂νZL) *
              (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L)) := by sorry
