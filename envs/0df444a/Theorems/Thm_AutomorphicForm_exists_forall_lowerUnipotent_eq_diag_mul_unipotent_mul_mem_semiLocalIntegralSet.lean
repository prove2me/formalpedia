-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_lowerUnipotent_eq_diag_mul_unipotent_mul_mem_semiLocalIntegralSet
-- name    : AutomorphicForm.exists_forall_lowerUnipotent_eq_diag_mul_unipotent_mul_mem_semiLocalIntegralSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/54b92afc-ee51-5987-9e06-28939ecbb61f
-- title:
--   Lower-unipotent absorption in GL₂(L⊗_K Kᵥ) with integrable weight
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $v$ be a nonzero prime of $\mathcal O_K$, and write $E = L\otimes_K K_v$ for the base change of $L$ to the $v$-adic completion $K_v$; equip $E$ with a measurable structure that is the Borel structure of its topology and let $\nu$ be an additive Haar measure on $E$. The assertion is that there exists a function $Y : E \to [0,\infty]$ which is measurable and whose lower Lebesgue integral satisfies $\int^- Y\,d\nu \neq \infty$, and which has the following property: for every $y \in E$ there are elements $\eta, t \in E$ with $\eta$ a unit of $E$ such that $Y(y) = \bigl(\|N_{E/K_v}(\eta^2)\|\bigr)^{-1}$, the norm being the $K_v$-algebra norm of $\eta^2$ and $\|\cdot\|$ its $v$-adic absolute value, passed through `ENNReal.ofReal` and inverted in $[0,\infty]$, and there is a $k$ in [`AutomorphicForm.semiLocalIntegralSet K L v`](def/AutomorphicForm_TwistedOrbital.html#L136), that is an element $k \in \mathrm{GL}_2(E)$ such that the matrix of $k$ and the matrix of $k^{-1}$ both lie in `integralMatrixSet` of the set `semiLocalIntegers K L v`, the image of `HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v`, for which the matrix identity
--   $$\begin{pmatrix}1&0\\ y&1\end{pmatrix} = \begin{pmatrix}\eta^{-1}&0\\ 0&\eta\end{pmatrix}\begin{pmatrix}1&t\\ 0&1\end{pmatrix}k$$
--   holds in $2\times 2$ matrices over $E$, the inverse of $\eta$ being taken as `Ring.inverse η`.
--
--   This is the Iwasawa-type big-cell statement for the semi-local group $\mathrm{GL}_2(L\otimes_K K_v)$: every lower unipotent element is rewritten as a split torus element times an upper unipotent element times an element of the semi-local integral set, with a weight $\|N(\eta^2)\|^{-1}$ that is $\nu$-integrable. It serves as the local input for the unfolding of twisted orbital integrals against indicator functions of the semi-local integral set, and is used in [`AutomorphicForm.exists_forall_norm_sub_norm_mul_le_mul_rpow_mul_log_pow_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_mul_mul`](thm.html#AutomorphicForm.exists_forall_norm_sub_norm_mul_le_mul_rpow_mul_log_pow_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_mul_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_lowerUnipotent_eq_diag_mul_unipotent_mul_mem_semiLocalIntegralSet.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal

theorem AutomorphicForm.exists_forall_lowerUnipotent_eq_diag_mul_unipotent_mul_mem_semiLocalIntegralSet
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] :
    ∃ Y : L ⊗[K] v.adicCompletion K → ℝ≥0∞, Measurable Y ∧ ∫⁻ y, Y y ∂ν ≠ ⊤ ∧
      ∀ y : L ⊗[K] v.adicCompletion K, ∃ η t : L ⊗[K] v.adicCompletion K, IsUnit η ∧
        Y y = (ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) (η ^ 2)‖)⁻¹ ∧
        ∃ k ∈ AutomorphicForm.semiLocalIntegralSet K L v,
          (!![1, 0; y, 1] : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
            !![Ring.inverse η, 0; 0, η] * !![1, t; 0, 1] * (k : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) := by sorry
