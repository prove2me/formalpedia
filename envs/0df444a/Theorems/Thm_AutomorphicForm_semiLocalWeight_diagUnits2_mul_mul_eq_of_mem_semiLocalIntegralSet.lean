-- Prove2me | Theorems.Thm_AutomorphicForm_semiLocalWeight_diagUnits2_mul_mul_eq_of_mem_semiLocalIntegralSet
-- name    : AutomorphicForm.semiLocalWeight_diagUnits2_mul_mul_eq_of_mem_semiLocalIntegralSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/3890cdcb-6db6-594e-b7a2-c1fb6656f35c
-- title:
--   Left-diagonal and right-integral invariance of the semi-local weight
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an algebra over $K$, and let $v$ be a nonzero prime of $\mathcal{O}_K$ (a point of the height-one spectrum). Write $E = L \otimes_K K_v$ for the base change of $L$ to the $v$-adic completion of $K$, and let $p_1, p_2 \in E^\times$, $x, k \in \mathrm{GL}_2(E)$. Assume $k$ lies in [`AutomorphicForm.semiLocalIntegralSet K L v`](def/AutomorphicForm_TwistedOrbital.html#L136), that is, both the matrix of $k$ and the matrix of $k^{-1}$ lie in `integralMatrixSet` of the set [`AutomorphicForm.semiLocalIntegers K L v`](def/AutomorphicForm_TwistedOrbital.html#L98), the range of `HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v` in $E$. Then $$\mathrm{semiLocalWeight}_{K,L,v}\big(\mathrm{diag}(p_1,p_2)\, x\, k\big) = \mathrm{semiLocalWeight}_{K,L,v}(x),$$ where $\mathrm{diag}(p_1,p_2)$ denotes the invertible matrix $\begin{pmatrix} p_1 & 0 \\ 0 & p_2\end{pmatrix}$ with its evident inverse, and where [`AutomorphicForm.semiLocalWeight K L v`](def/AutomorphicForm_WeightedOrbitalRelation.html#L81) is the finite sum, over the primes $w$ of $\mathcal{O}_L$ lying under $v$, of $\mathrm{LocalWeight.weight}$ of the image of the argument in $\mathrm{GL}_2(L_w)$ under the base-change identification of $E$ with $\prod_{w \mid v} L_w$ followed by evaluation at $w$; here $\mathrm{LocalWeight.weight}(g) = 2\log\big(\max(\|g_{00}\|,\|g_{01}\|)\cdot \mathrm{AdelicHeight.rowMaxNorm}(g)/\|\det g\|\big)$.
--
--   This is the invariance of the semi-local weight factor under left translation by the diagonal torus and right translation by the integral (maximal compact) subgroup, the property that makes the weight well defined on the Iwasawa coordinates of $\mathrm{GL}_2(E)$. It is used in evaluating the twisted weighted orbital integral in Iwasawa coordinates, where the weight reduces to a sum of local terms $2\log^+\|\xi_w\|_w$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_semiLocalWeight_diagUnits2_mul_mul_eq_of_mem_semiLocalIntegralSet.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.semiLocalWeight_diagUnits2_mul_mul_eq_of_mem_semiLocalIntegralSet
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (p₁ p₂ : (L ⊗[K] v.adicCompletion K)ˣ) (x k : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (hk : k ∈ AutomorphicForm.semiLocalIntegralSet K L v) :
    AutomorphicForm.semiLocalWeight K L v (diagUnits2 p₁ p₂ * x * k) = AutomorphicForm.semiLocalWeight K L v x := by sorry
