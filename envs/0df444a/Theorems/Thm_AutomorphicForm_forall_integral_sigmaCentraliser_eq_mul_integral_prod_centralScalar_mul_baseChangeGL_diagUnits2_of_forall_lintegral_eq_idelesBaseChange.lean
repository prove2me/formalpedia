-- Prove2me | Theorems.Thm_AutomorphicForm_forall_integral_sigmaCentraliser_eq_mul_integral_prod_centralScalar_mul_baseChangeGL_diagUnits2_of_forall_lintegral_eq_idelesBaseChange
-- name    : AutomorphicForm.forall_integral_sigmaCentraliser_eq_mul_integral_prod_centralScalar_mul_baseChangeGL_diagUnits2_of_forall_lintegral_eq_idelesBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/cefbf662-49c4-50b9-889b-c30f0e2668c2
-- title:
--   Torus constant c_H: lower-integral form implies Bochner form
-- statement:
--   Let $K \subseteq L$ be number fields, and let the idele groups $(\mathbb{A}_L)^\times$ and $(\mathbb{A}_K)^\times$ carry Borel measurable structures together with Haar measures $\nu_{ZL}$ and $\nu_K$ respectively. Let $H$ be a subgroup of $\mathrm{GL}_2(\mathbb{A}_L)$ whose underlying set is closed, equipped with a measure $\mu_H$ that is both a Haar measure and right multiplication invariant, and let $c_H$ be a real number with $c_H > 0$. Assume that for every measurable $f : \mathrm{GL}_2(\mathbb{A}_L) \to [0,\infty]$ the lower Lebesgue integral of $f$ restricted to $H$ against $\mu_H$ equals $c_H$ (as an extended nonnegative real) times the iterated lower integral $\int^{-}_{z}\int^{-}_{a} f\bigl(z\cdot I_2 \cdot \mathrm{diag}(\beta(a),1)\bigr)\,d\nu_K(a)\,d\nu_{ZL}(z)$, where $z \cdot I_2$ denotes the scalar matrix attached to $z \in (\mathbb{A}_L)^\times$, $\mathrm{diag}(\cdot,1)$ the embedding $u \mapsto \mathrm{diag}(u,1)$, and $\beta : (\mathbb{A}_K)^\times \to (\mathbb{A}_L)^\times$ the unit map induced by the ring homomorphism $\mathbb{A}_K \to \mathbb{A}_L$ of [`M4aHerbrand.GenuineDescent.genuineBaseChange`](def/M4aHerbrand_GenuineDescent.html#L87). Then for every function $g : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$, with no measurability or integrability hypothesis, the Bochner integral of $g$ over $H$ against $\mu_H$ equals $c_H$ times the Bochner integral over the product measure $\nu_{ZL} \times \nu_K$ of $(z,a) \mapsto g\bigl(z \cdot I_2 \cdot \mathrm{bc}(\iota(\mathrm{diag}(a,1)))\bigr)$, where $\iota$ sends $\mathrm{diag}(a,1) \in \mathrm{GL}_2(\mathbb{A}_K)$ to $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ by the right tensor inclusion and $\mathrm{bc}$ is induced by the ring isomorphism $L \otimes_K \mathbb{A}_K \cong \mathbb{A}_L$.
--
--   The statement converts a characterisation of the constant $c_H$ governing the measure of the base-change torus shell from the lower-integral normalisation, with the torus parametrised through the idelic base change $\beta$ and $\mathrm{diag}(\cdot,1)$, into the Bochner normalisation, with the torus parametrised through the tensor description $L \otimes_K \mathbb{A}_K \cong \mathbb{A}_L$ of base change; the same constant $c_H$ occurs on both sides. It is used in the assembly of the hyperbolic comparison, where the two normalisations of $c_H$ must be matched so that the constant cancels.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_forall_integral_sigmaCentraliser_eq_mul_integral_prod_centralScalar_mul_baseChangeGL_diagUnits2_of_forall_lintegral_eq_idelesBaseChange.lean

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
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.forall_integral_sigmaCentraliser_eq_mul_integral_prod_centralScalar_mul_baseChangeGL_diagUnits2_of_forall_lintegral_eq_idelesBaseChange
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νK.IsHaarMeasure]
    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (cH : ℝ) (hcH : 0 < cH)
    (hμH : ∀ f : AdelicGL2 (𝓞 L) L → ENNReal, Measurable f →
      ∫⁻ h : H, f (h : AdelicGL2 (𝓞 L) L) ∂μH =
        ENNReal.ofReal cH * ∫⁻ z, ∫⁻ a, f (AutomorphicForm.centralScalar (𝓞 L) L z *
          diagOne ((Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom) a)) ∂νK ∂νZL) :
    ∀ g : AdelicGL2 (𝓞 L) L → ℂ,
      ∫ h : H, g (h : AdelicGL2 (𝓞 L) L) ∂μH =
        cH * ∫ p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ,
          g (AutomorphicForm.centralScalar (𝓞 L) L p.1 *
            AutomorphicForm.baseChangeGL K L
              (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.2 1))) ∂(νZL.prod νK) := by sorry
