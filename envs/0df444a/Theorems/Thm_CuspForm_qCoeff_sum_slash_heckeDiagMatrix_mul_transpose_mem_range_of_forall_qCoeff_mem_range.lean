-- Prove2me | Theorems.Thm_CuspForm_qCoeff_sum_slash_heckeDiagMatrix_mul_transpose_mem_range_of_forall_qCoeff_mem_range
-- name    : CuspForm.qCoeff_sum_slash_heckeDiagMatrix_mul_transpose_mem_range_of_forall_qCoeff_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/383a6265-287b-55fb-afcc-9558f738f020
-- title:
--   Transposed Uᵣ preserves rationality of q-coefficients
-- statement:
--   Fix a positive integer $M$, a subgroup $H \le (\mathbb{Z}/M\mathbb{Z})^\times$, a prime $r$ dividing $M$, and a weight $k \in \mathbb{Z}$. Let $\Gamma_H(M) \le \mathrm{SL}_2(\mathbb{Z})$ be the group [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), namely the image in $\mathrm{SL}_2(\mathbb{Z})$ of those $\gamma \in \Gamma_0(M)$ whose lower-right entry reduces mod $M$ to an element of $H$, viewed as a subgroup of $\mathrm{GL}_2(\mathbb{R})$, and let $g$ be a cusp form of weight $k$ for it. Assume that for every $n$ the coefficient [`ModularFormClass.qCoeff`](def/FLTPrelim_Modularity.html#L19) $(g)(n)$, i.e. the $n$-th coefficient of the $q$-expansion of $g$ at $\infty$ of width $1$, lies in the image of $\mathbb{Q}$ in $\mathbb{C}$. The conclusion is that for every $n$ the $n$-th such coefficient of the function
--   $$\sum_{j=0}^{r-1} g \mid_k \left( \begin{pmatrix} r & 0 \\ 0 & 1 \end{pmatrix} \begin{pmatrix} 1 & 0 \\ Mj & 1 \end{pmatrix} \right)$$
--   again lies in the image of $\mathbb{Q}$ in $\mathbb{C}$. Here $\mid_k$ is the weight-$k$ slash action of $\mathrm{GL}_2(\mathbb{R})$, [`ModularForm.heckeDiagMatrix r`](def/ModularForm_HeckeOperator.html#L21) is the upper triangular matrix with diagonal $(r,1)$ and zero off-diagonal entry, and the second factor is the transpose of $T^{Mj}$ with $T = \begin{pmatrix} 1 & 1 \\ 0 & 1\end{pmatrix}$; the sum is formed as a function on the upper half-plane, not as a cusp form.
--
--   The operator appearing here is the transposed (dual) Hecke operator $U_r^{t} = w_M U_r w_M^{-1}$ at a prime $r$ dividing the level, given by the coset representatives $\begin{pmatrix} r & 0 \\ Mj & 1\end{pmatrix}$, $0 \le j < r$; the statement is the rationality of its $q$-expansion at $\infty$. It feeds into [`CuspForm.mem_twoCuspIntegralSet_range_of_coe_eq_sum_slash_transpose_of_mem_twoCuspIntegralSet_range`](thm.html#CuspForm.mem_twoCuspIntegralSet_range_of_coe_eq_sum_slash_transpose_of_mem_twoCuspIntegralSet_range) in the analysis of integrality at the two cusps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_qCoeff_sum_slash_heckeDiagMatrix_mul_transpose_mem_range_of_forall_qCoeff_mem_range.lean

import Mathlib
import Definitions.Def_CuspForm_TwoCuspLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.qCoeff_sum_slash_heckeDiagMatrix_mul_transpose_mem_range_of_forall_qCoeff_mem_range
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (r : ℕ) (hr : r.Prime) (hrM : r ∣ M) (k : ℤ)
    (g : CuspForm (CohCarrier.GammaH M H) k)
    (hg : ∀ n : ℕ, ModularFormClass.qCoeff (⇑g) n ∈ (algebraMap ℚ ℂ).range) :
    ∀ n : ℕ, ModularFormClass.qCoeff
        (∑ j ∈ Finset.range r,
          (⇑g) ∣[k] (ModularForm.heckeDiagMatrix r *
            (Matrix.SpecialLinearGroup.mapGL ℝ
              (Matrix.SpecialLinearGroup.transpose (ModularGroup.T ^ (M * j))) : GL (Fin 2) ℝ))) n ∈
      (algebraMap ℚ ℂ).range := by sorry
