-- Prove2me | Theorems.Thm_AutomorphicForm_isHaarMeasure_and_isMulRightInvariant_unipotentHaar
-- name    : AutomorphicForm.isHaarMeasure_and_isMulRightInvariant_unipotentHaar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/78cdbaa9-ae3a-5d5d-9ea0-86a03a05d73e
-- title:
--   Normalised unipotent adelic measure is a bi-invariant Haar measure
-- statement:
--   Let $K$ be a number field, with ring of integers $\mathcal{O}_K$ and adele ring $\mathbb{A}_K$; the group $\mathrm{GL}_2(\mathbb{A}_K)$ carries the Borel $\sigma$-algebra `glBorel`, and $\mathbb{A}_K$ the $\sigma$-algebra `adeleBorel`, for which `adelicAddHaar` is its additive Haar measure. Let `adelicUnipotent K` be the subgroup of $\mathrm{GL}_2(\mathbb{A}_K)$ given by the range of the homomorphism `unipotentGL2Hom` defined over $\mathbb{A}_K$, and let `toAdelicUnipotent K` be the map sending an adele $x$ to the element of that range obtained by applying `unipotentGL2Hom` to $x$ regarded multiplicatively via `Multiplicative.ofAdd`. The measure `unipotentHaar K` on `adelicUnipotent K` is the pushforward along `toAdelicUnipotent K` of the additive Haar measure of $\mathbb{A}_K$ rescaled by the inverse of its mass on the box `adelicBox K`, the set of adeles whose archimedean component lies in `infiniteBox K` and whose finite component lies in the integral finite adeles `integralFiniteAdeles (𝓞 K) K`. The assertion is the conjunction of two statements: this measure is a Haar measure on `adelicUnipotent K`, and it is invariant under right translations.
--
--   This fixes the normalisation of Haar measure on the adelic unipotent subgroup $N(\mathbb{A}_K) \subset \mathrm{GL}_2(\mathbb{A}_K)$, the total mass being $1$ on the standard box, together with the (abelian) bi-invariance needed to translate integrals on both sides. It is used throughout the measure-theoretic estimates of the automorphic-forms development, for instance in the class-sum growth bounds and in the comparison of window masses for isotypic cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isHaarMeasure_and_isMulRightInvariant_unipotentHaar.lean

import Definitions.Def_AutomorphicForm_UnipotentQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.isHaarMeasure_and_isMulRightInvariant_unipotentHaar (K : Type*) [Field K]
    [NumberField K] :
    (AutomorphicForm.unipotentHaar K).IsHaarMeasure ∧
      (AutomorphicForm.unipotentHaar K).IsMulRightInvariant := by sorry
