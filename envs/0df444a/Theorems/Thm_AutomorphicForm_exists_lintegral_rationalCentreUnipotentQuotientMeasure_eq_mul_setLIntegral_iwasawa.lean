-- Prove2me | Theorems.Thm_AutomorphicForm_exists_lintegral_rationalCentreUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa
-- name    : AutomorphicForm.exists_lintegral_rationalCentreUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/f94ae75d-7226-5d11-804d-46c996300a44
-- title:
--   Iwasawa disintegration of the Z(K)N(A)-quotient measure on GL₂
-- statement:
--   Let $K$ be a number field, with adele ring $\mathbb{A} =$ `AdeleRing (𝓞 K) K` and $\mathrm{GL}_2(\mathbb{A}) =$ `AdelicGL2 (𝓞 K) K`; all spaces carry their Borel structures. The assertion is that there exists a constant $c \in [0,\infty]$ with $c \neq 0$ and $c \neq \infty$, independent of the data below, such that the following holds. Let $D$ be a measurable subset of the idele group $\mathbb{A}^{\times}$ which is a fundamental domain, for the Haar measure [`NumberField.Idele.idelicHaar K`](def/NumberField_IdeleProductMeasure.html#L391), for the action of the subgroup [`M4aHerbrand.principalIdeles (𝓞 K) K`](def/M4aHerbrand_IdeleClassVocab.html#L16) of principal ideles, that is the image of $K^{\times}$ under the map of unit groups induced by $K \to \mathbb{A}$. Let $f \colon \mathrm{GL}_2(\mathbb{A}) \to [0,\infty]$ be measurable and invariant under left multiplication by every element of the subgroup `rationalCentreUnipotent K`, the join `rationalCentre K ⊔ adelicUnipotent K`. Then the lower Lebesgue integral of $q \mapsto f(q.\mathrm{out})$, over the quotient `RationalCentreUnipotentQuotient K` with respect to the quotient measure `rationalCentreUnipotentQuotientMeasure K` obtained from the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` and the measure `rationalCentreUnipotentHaar K` on that subgroup, equals $c$ times the iterated integral, over $z \in D$ and $t \in \mathbb{A}^{\times}$ for `idelicHaar K` and over $k$ in the subgroup `adelicMaximalCompact K` (those $k$ whose finite part lies in `finiteIntegralGL2 (𝓞 K) K` and whose component at each infinite place is a row isometry) for its Haar measure `maximalCompactHaar K`, of $f(\mathrm{diag}(z,z) \cdot \mathrm{diag}(t,1) \cdot k)$ multiplied by $\mathrm{ofReal}\big((\|t\|)^{-1}\big)$, where $\|t\|$ is [`NumberField.TateGlobal.ideleNorm K t`](def/NumberField_TateGlobalZeta.html#L19), the module of the Haar character of $\mathbb{A}$ at $t$. Both sides may be infinite.
--
--   This is the Iwasawa-coordinate disintegration of the quotient measure on $Z(K)N(\mathbb{A})\backslash\mathrm{GL}_2(\mathbb{A})$: an integral over the quotient of a left $Z(K)N(\mathbb{A})$-invariant function is rewritten as an integral over a fundamental domain for $K^\times$ in the ideles, the full idele group with weight $\|t\|^{-1}$, and the standard maximal compact subgroup. It supplies the measure-theoretic step of Rankin–Selberg unfolding and is used in the construction of test data with non-vanishing, analytically continued $s$-part integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_lintegral_rationalCentreUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa.lean

import Definitions.Def_AutomorphicForm_RationalCentreUnipotentQuotient
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem AutomorphicForm.exists_lintegral_rationalCentreUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa
    (K : Type) [Field K] [NumberField K] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      ∀ (D : Set (AdeleRing (𝓞 K) K)ˣ), MeasurableSet D →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K) →
      ∀ f : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable f →
        (∀ x ∈ rationalCentreUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g) →
        ∫⁻ q, f q.out ∂(rationalCentreUnipotentQuotientMeasure K) =
          c * ∫⁻ z in D, ∫⁻ t, ∫⁻ k,
                f (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
              ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) := by sorry
