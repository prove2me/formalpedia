-- Prove2me | Theorems.Thm_AutomorphicForm_exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa
-- name    : AutomorphicForm.exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/bc8dc965-c2bc-5697-add6-e1dada10c39d
-- title:
--   Iwasawa formula for the T(K)N(A)-quotient measure
-- statement:
--   Let $K$ be a number field, with $\mathbb{A}_K$ its adele ring and $G = \mathrm{GL}_2(\mathbb{A}_K)$, all relevant spaces carrying their Borel structures. The assertion is that there exists $c \in [0,\infty]$ with $c \neq 0$ and $c \neq \infty$ such that the following holds for all measurable subsets $D, D'$ of the idele group $\mathbb{A}_K^\times$, each a fundamental domain, for the action of the subgroup [`M4aHerbrand.principalIdeles`](def/M4aHerbrand_IdeleClassVocab.html#L16) of principal ideles (the image of $K^\times$ under the unit map induced by $K \to \mathbb{A}_K$), with respect to the Haar measure [`NumberField.Idele.idelicHaar`](def/NumberField_IdeleProductMeasure.html#L391) on $\mathbb{A}_K^\times$, and for every measurable $f : G \to [0,\infty]$ satisfying $f(xg) = f(g)$ for every $x$ in the subgroup `rationalTorusUnipotent` $K$, the join of `rationalTorus` $K$ and `adelicUnipotent` $K$, and every $g \in G$: the integral of $f$ evaluated at chosen coset representatives $q.\mathrm{out}$, against `rationalTorusUnipotentQuotientMeasure` $K$ (the quotient measure obtained from the adelic Haar measure on $G$ and the chosen Haar measure on `rationalTorusUnipotent` $K$), equals $c$ times the iterated integral, over $z \in D$ and $t \in D'$ with respect to `idelicHaar` and over $k$ with respect to the Haar measure `maximalCompactHaar` $K$ on the adelic maximal compact subgroup (matrices whose finite part is integral and whose archimedean components act as row isometries), of $f(\mathrm{diag}(z,z)\,\mathrm{diag}(t,1)\,k)$ times $\|t\|^{-1}$, where $\|t\|$ is the idelic norm given by the distributive Haar character of $\mathbb{A}_K$.
--
--   This is the unfolding of the quotient measure on $T(K)N(\mathbb{A}_K)\backslash \mathrm{GL}_2(\mathbb{A}_K)$ in Iwasawa coordinates, reducing integrals of left $T(K)N(\mathbb{A}_K)$-invariant functions to integrals over two fundamental domains for $K^\times$ in the ideles and over the maximal compact subgroup. It is used in the estimates for class sums and in the computation of inner products of pseudo-Eisenstein series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa.lean

import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
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

theorem AutomorphicForm.exists_lintegral_rationalTorusUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa
    (K : Type) [Field K] [NumberField K] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      ∀ (D D' : Set (AdeleRing (𝓞 K) K)ˣ), MeasurableSet D → MeasurableSet D' →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K) →
        IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D' (NumberField.Idele.idelicHaar K) →
      ∀ f : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable f →
        (∀ x ∈ rationalTorusUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, f (x * g) = f g) →
        ∫⁻ q, f q.out ∂(rationalTorusUnipotentQuotientMeasure K) =
          c * ∫⁻ z in D, ∫⁻ t in D', ∫⁻ k,
                f (centralScalar (𝓞 K) K z * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
              ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) := by sorry
