-- Prove2me | Theorems.Thm_AutomorphicForm_exists_trace_eq_one_tmul_and_det_eq_one_tmul_and_norm_sq_le_of_forall_isUnit
-- name    : AutomorphicForm.exists_trace_eq_one_tmul_and_det_eq_one_tmul_and_norm_sq_le_of_forall_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/d36aeb4e-292b-5c00-8d2e-8c6f756798c6
-- title:
--   Trace and determinant on a twisted commutant are Kᵥ-scalars
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra of degree $\operatorname{finrank}_K L = 2$, and let $\sigma$ be a $K$-algebra automorphism of $L$ such that every $K$-algebra automorphism $\tau$ of $L$ lies in the subgroup of integer powers of $\sigma$. Let $v$ be a nonzero prime ideal of the ring of integers $\mathcal{O}_K$, with completion $K_v =$ `v.adicCompletion K`, carrying its normalised absolute value $\lVert\cdot\rVert$, and put $E_v = L \otimes_K K_v$. Let $\delta \in \mathrm{GL}_2(E_v)$ and write $\mathcal{D}$ for the $\sigma$-twisted commutant of $\delta$, that is the $K$-subalgebra of $M_2(E_v)$ consisting of those $X$ with $X\delta = \delta \cdot X^{\sigma}$, where $X^{\sigma}$ is obtained by applying the ring homomorphism $\sigma \otimes \mathrm{id}_{K_v}$ of $E_v$ to each entry. Assume every nonzero element of $\mathcal{D}$ is a unit of $M_2(E_v)$. Then for every $X \in \mathcal{D}$ there exist $t, n \in K_v$ with $\operatorname{tr} X = 1 \otimes t$, $\det X = 1 \otimes n$ and $\lVert t\rVert^2 \le \lVert n\rVert$.
--
--   The twisted commutant of $\delta$ is, under the stated invertibility hypothesis, a quaternion division algebra over $K_v$, and the statement identifies the matrix trace and determinant of its elements with the reduced trace and reduced norm, both scalars in $1 \otimes K_v$, together with the non-archimedean inequality $\lVert \mathrm{trd}\, X\rVert^2 \le \lVert \mathrm{nrd}\, X\rVert$. It is used to show that the elements of integral reduced norm form a subring, and feeds the local computations of reduced norms and traces behind the orbital integrals attached to automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_trace_eq_one_tmul_and_det_eq_one_tmul_and_norm_sq_le_of_forall_isUnit.lean

import Definitions.Def_AutomorphicForm_TwistedCommutant
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal

theorem AutomorphicForm.exists_trace_eq_one_tmul_and_det_eq_one_tmul_and_norm_sq_le_of_forall_isUnit
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hdiv : ∀ X ∈ twistedCommutant K L (v.adicCompletion K) σ δ, X ≠ 0 → IsUnit X)
    (X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hX : X ∈ twistedCommutant K L (v.adicCompletion K) σ δ) :
    ∃ t n : v.adicCompletion K,
      X.trace = (1 : L) ⊗ₜ[K] t ∧ X.det = (1 : L) ⊗ₜ[K] n ∧ ‖t‖ ^ 2 ≤ ‖n‖ := by sorry
