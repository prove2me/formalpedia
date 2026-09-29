-- Prove2me | Theorems.Thm_AutomorphicForm_isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant
-- name    : AutomorphicForm.isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/94bdcc9f-aa90-511c-b1c3-9b46c58e593e
-- title:
--   Z(K)N(A_K)-measure is a left and right invariant Haar measure
-- statement:
--   Let $K$ be a number field. Inside $\mathrm{GL}_2(\mathbb{A}_K)$, written `AdelicGL2 (𝓞 K) K` and carrying the Borel $\sigma$-algebra of its topology (the adele ring likewise), consider the subgroup `rationalCentreUnipotent K`, the join `rationalCentre K ⊔ adelicUnipotent K` of the subgroup `rationalCentre K` and the image `adelicUnipotent K` of the unipotent homomorphism `unipotentGL2Hom` over $\mathbb{A}_K$. On this subgroup, `rationalCentreUnipotentHaar K` is the measure obtained as the sum, over $a \in K^\times$, of the pushforwards of `unipotentHaar K` along the maps sending an adelic unipotent $n$ to the product of the global point attached to the scalar matrix $a \cdot I$ with $n$; here `unipotentHaar K` is the pushforward along `toAdelicUnipotent K` of the additive Haar measure of $\mathbb{A}_K$ rescaled so that `adelicBox K` has mass $1$. The theorem asserts the conjunction: this measure is a Haar measure on `rationalCentreUnipotent K` (left invariant, finite on compact sets, positive on non-empty open sets) and it is in addition right invariant.
--
--   This supplies the measure on $Z(K)N(\mathbb{A}_K)$, a countable disjoint union of translates of the normalised Haar measure of $N(\mathbb{A}_K) \cong \mathbb{A}_K$, together with the invariance properties needed to integrate over the quotient $Z(K)N(\mathbb{A}_K) \backslash \mathrm{GL}_2(\mathbb{A}_K)$. It is used in the Iwasawa-coordinate and Rankin–Selberg integral computations, for instance in [`AutomorphicForm.exists_lintegral_rationalCentreUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa`](thm.html#AutomorphicForm.exists_lintegral_rationalCentreUnipotentQuotientMeasure_eq_mul_setLIntegral_iwasawa) and [`AutomorphicForm.integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient`](thm.html#AutomorphicForm.integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant.lean

import Definitions.Def_AutomorphicForm_RationalCentreUnipotentQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem AutomorphicForm.isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant
    (K : Type) [Field K] [NumberField K] :
    (rationalCentreUnipotentHaar K).IsHaarMeasure ∧ (rationalCentreUnipotentHaar K).IsMulRightInvariant := by sorry
