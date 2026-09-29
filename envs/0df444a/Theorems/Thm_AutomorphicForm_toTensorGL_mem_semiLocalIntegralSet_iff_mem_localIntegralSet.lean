-- Prove2me | Theorems.Thm_AutomorphicForm_toTensorGL_mem_semiLocalIntegralSet_iff_mem_localIntegralSet
-- name    : AutomorphicForm.toTensorGL_mem_semiLocalIntegralSet_iff_mem_localIntegralSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/93c353af-d4ff-5e72-a98f-4830ec05b3b0
-- title:
--   Integrality descends along GL₂(Kᵥ)toGL₂(L⊗_K Kᵥ)
-- statement:
--   Let $K$ and $L$ be number fields (each a field with a `NumberField` instance) with $L$ a $K$-algebra, let $v$ be a height-one prime of the ring of integers $\mathcal{O}_K$, and let $s$ be an element of $\mathrm{GL}_2(K_v)$, where $K_v$ denotes `v.adicCompletion K`. Write $\iota =$ [`AutomorphicForm.toTensorGL K L (v.adicCompletion K)`](def/AutomorphicForm_TwistedOrbital.html#L71) for the group homomorphism $\mathrm{GL}_2(K_v)\to\mathrm{GL}_2(L\otimes_K K_v)$ obtained by applying the functor $\mathrm{GL}_2$ to the $K$-algebra map $\mathrm{includeRight}\colon K_v\to L\otimes_K K_v$, $x\mapsto 1\otimes x$. The assertion is that $\iota(s)$ belongs to [`AutomorphicForm.semiLocalIntegralSet K L v`](def/AutomorphicForm_TwistedOrbital.html#L136) if and only if $s$ belongs to [`AutomorphicForm.localIntegralSet K v`](def/AutomorphicForm_LocalOrbitalBase.html#L100). Here the first set is `integralUnitsSet` of the subset `semiLocalIntegers K L v` of $L\otimes_K K_v$, namely the range of `HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v`, i.e. the image of $\mathcal{O}_L\otimes\mathcal{O}_{K_v}$; and the second is `integralUnitsSet` of the subring $\mathcal{O}_{K_v}$ of $v$-adic integers in $K_v$. In both cases `integralUnitsSet U` consists of those invertible matrices $g$ for which the matrix of $g$ and the matrix of $g^{-1}$ both lie in `integralMatrixSet U`.
--
--   This is the statement that the standard maximal compact integrality condition at $v$ is detected by base change to the semi-local algebra $L\otimes_K K_v\cong\prod_{w\mid v}L_w$: a matrix over $K_v$ is integral over $L\otimes_K K_v$ exactly when it is integral over $\mathcal{O}_{K_v}$. It is used in the normalisation of transported torus measures and in the double-coset bounds for twisted orbital integrals of indicator functions of the semi-local integral set.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_toTensorGL_mem_semiLocalIntegralSet_iff_mem_localIntegralSet.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Pointwise
open scoped TensorProduct.RightActions

theorem AutomorphicForm.toTensorGL_mem_semiLocalIntegralSet_iff_mem_localIntegralSet
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (s : GL (Fin 2) (v.adicCompletion K)) :
    AutomorphicForm.toTensorGL K L (v.adicCompletion K) s ∈ AutomorphicForm.semiLocalIntegralSet K L v ↔
      s ∈ AutomorphicForm.localIntegralSet K v := by sorry
