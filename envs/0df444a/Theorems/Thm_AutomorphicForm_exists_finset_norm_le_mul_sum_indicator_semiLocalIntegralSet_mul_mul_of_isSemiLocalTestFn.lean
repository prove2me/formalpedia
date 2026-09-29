-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_norm_le_mul_sum_indicator_semiLocalIntegralSet_mul_mul_of_isSemiLocalTestFn
-- name    : AutomorphicForm.exists_finset_norm_le_mul_sum_indicator_semiLocalIntegralSet_mul_mul_of_isSemiLocalTestFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/2f3220e7-ecdd-5797-abac-f595c31eac21
-- title:
--   Semi-local test functions dominated by finitely many double-coset indicators
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $v$ be a nonzero prime of the ring of integers $\mathcal{O}_K$, and write $E_v = L \otimes_K K_v$ for the tensor product of $L$ with the $v$-adic completion of $K$. Let $\varphi_v : \mathrm{GL}_2(E_v) \to \mathbb{C}$ satisfy [`AutomorphicForm.IsSemiLocalTestFn K L v`](def/AutomorphicForm_TwistedOrbital.html#L130), that is, $\varphi_v$ is locally constant and has compact support. Write $\mathcal{K}_v =$ [`AutomorphicForm.semiLocalIntegralSet K L v`](def/AutomorphicForm_TwistedOrbital.html#L136) for the set of $g \in \mathrm{GL}_2(E_v)$ such that both the matrix of $g$ and the matrix of $g^{-1}$ lie in `integralMatrixSet` of the set `semiLocalIntegers K L v`, the latter being the range of the canonical map `HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v` into $E_v$. The assertion is that there exist a real number $M \ge 0$ and a finite set $s$ of elements of $\mathrm{GL}_2(E_v)$ such that for every $g \in \mathrm{GL}_2(E_v)$,
--   $$\|\varphi_v(g)\| \le M \sum_{a \in s} \mathbf{1}_{\mathcal{K}_v \cdot \{a\} \cdot \mathcal{K}_v}(g),$$
--   the products being pointwise products of subsets of $\mathrm{GL}_2(E_v)$ and the indicators taking the real values $1$ and $0$.
--
--   This is the elementary domination step for semi-local test functions: a locally constant, compactly supported function on $\mathrm{GL}_2(L \otimes_K K_v)$ is bounded by a constant multiple of a finite sum of indicators of double cosets of the integral subset $\mathcal{K}_v$. It is used in [`AutomorphicForm.exists_forall_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_of_isSemiLocalTestFn`](thm.html#AutomorphicForm.exists_forall_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_of_isSemiLocalTestFn), where twisted orbital integrals of such test functions are estimated.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_norm_le_mul_sum_indicator_semiLocalIntegralSet_mul_mul_of_isSemiLocalTestFn.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Pointwise
open scoped TensorProduct.RightActions

theorem AutomorphicForm.exists_finset_norm_le_mul_sum_indicator_semiLocalIntegralSet_mul_mul_of_isSemiLocalTestFn
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφv : AutomorphicForm.IsSemiLocalTestFn K L v φv) :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ s : Finset (GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      ∀ g : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        ‖φv g‖ ≤ M * ∑ a ∈ s,
          (AutomorphicForm.semiLocalIntegralSet K L v * {a} * AutomorphicForm.semiLocalIntegralSet K L v).indicator
            (fun _ => (1 : ℝ)) g := by sorry
