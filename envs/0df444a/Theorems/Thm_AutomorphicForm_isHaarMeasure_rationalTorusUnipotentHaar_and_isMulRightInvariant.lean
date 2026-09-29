-- Prove2me | Theorems.Thm_AutomorphicForm_isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant
-- name    : AutomorphicForm.isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/a6e1690b-5f8f-5bdc-9304-d269099f124f
-- title:
--   Unimodular Haar measure on T(K)N(A_K)
-- statement:
--   Let $K$ be a number field. Inside $GL_2(\mathbb{A}_K)$, written `AdelicGL2 (𝓞 K) K`, consider the subgroup `rationalTorusUnipotent K` obtained as the join $\mathrm{rationalTorus}(K) \sqcup N(\mathbb{A}_K)$, where $N(\mathbb{A}_K)$ is `adelicUnipotent K`, the range of the unipotent embedding `unipotentGL2Hom` over the adele ring, and `rationalTorus K` is a subgroup containing, for all $z,a\in K^{\times}$, the images under `globalPoints` (the map induced on $GL_2$ by $K \to \mathbb{A}_K$) of the scalar matrix $z\cdot 1$ and of $\mathrm{diag}(a,1)$. Both $\mathbb{A}_K$ and $GL_2(\mathbb{A}_K)$ carry their Borel $\sigma$-algebras, and the subgroup carries the induced structure. The measure `rationalTorusUnipotentHaar K` is the sum, over pairs $(z,a)\in K^{\times}\times K^{\times}$, of the pushforwards of `unipotentHaar K` along $n \mapsto (z\cdot 1)\,\mathrm{diag}(a,1)\,n$; here `unipotentHaar K` is the transport to $N(\mathbb{A}_K)$, along `toAdelicUnipotent K`, of the additive Haar measure of $\mathbb{A}_K$ rescaled by the inverse of the measure of `adelicBox K`. The assertion is the conjunction of two facts about this measure: it is a Haar measure on `rationalTorusUnipotent K`, that is, left invariant, finite on compact sets and positive on non-empty open sets, and it is in addition invariant under right translations.
--
--   This is the construction of the Haar measure of the mixed group $T(K)N(\mathbb{A}_K)$, as a sum of sheet measures indexed by the rational torus, together with its unimodularity; right invariance rests on the product formula for principal ideles, and local finiteness on the discreteness of $K$ in $\mathbb{A}_K$. It underlies the invariant measure on $T(K)N(\mathbb{A}_K)\backslash GL_2(\mathbb{A}_K)$ used in the torus-unfolding stage, and is cited by the estimates for pseudo-Eisenstein norms and for the growth of class sums.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant.lean

import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Mathlib.MeasureTheory.Group.FundamentalDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem AutomorphicForm.isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant
    (K : Type) [Field K] [NumberField K] :
    (rationalTorusUnipotentHaar K).IsHaarMeasure ∧ (rationalTorusUnipotentHaar K).IsMulRightInvariant := by sorry
