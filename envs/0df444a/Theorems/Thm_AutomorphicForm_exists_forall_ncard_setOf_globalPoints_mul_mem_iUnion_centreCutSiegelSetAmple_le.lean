-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_ncard_setOf_globalPoints_mul_mem_iUnion_centreCutSiegelSetAmple_le
-- name    : AutomorphicForm.exists_forall_ncard_setOf_globalPoints_mul_mem_iUnion_centreCutSiegelSetAmple_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/3db239d2-f2de-55db-a4f9-ad83f5d33d0c
-- title:
--   Uniformly bounded multiplicity of finitely many ample Siegel translates
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2,\kappa$ be real numbers with $1\le\kappa$, $0<c$ and $0<d_1$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb A_F)$, the group of invertible $2\times 2$ matrices over the adele ring of $F$. Write $\mathfrak S =$ `centreCutSiegelSetAmple F c u d₁ d₂ κ` for the set of $g\in\mathrm{GL}_2(\mathbb A_F)$ whose finite part lies in `finiteIntegralGL2`, whose archimedean local heights $\mathrm{localHeight}$ (the absolute value of the determinant divided by `rowNormSq`) at the component of $g$ at each infinite place $w$ of $F$ are at least $c$, whose window quantity `xWindowSq` at each infinite place is at most $u^2$, whose archimedean determinant norms `archDetNorm` at each infinite place lie in $[d_1,d_2]$, and which in addition satisfy the ampleness comparison $\mathrm{localHeight}$ at $w$ $\le\kappa\cdot\mathrm{localHeight}$ at $w'$ for all pairs of infinite places $w,w'$. The assertion is that there exists a natural number $N$ such that for every $h\in\mathrm{GL}_2(\mathbb A_F)$ the set of $\gamma\in\mathrm{GL}_2(F)$ whose image under the adelic embedding `globalPoints` satisfies $\gamma h\in\bigcup_{x\in T}\mathfrak S x$ is finite and has cardinality at most $N$; the bound $N$ is independent of $h$.
--
--   This is the bounded-multiplicity (Siegel) property in the form used downstream: the window $\bigcup_{x\in T}\mathfrak S x$ meets each right coset $\mathrm{GL}_2(F)h$ in a uniformly bounded number of points. It is invoked when $L^2$-integrals and suprema of adelic automorphic forms are compared across two covering windows, and when coverings modulo the centre are combined with approximation statements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_ncard_setOf_globalPoints_mul_mem_iUnion_centreCutSiegelSetAmple_le.lean

import Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel

theorem AutomorphicForm.exists_forall_ncard_setOf_globalPoints_mul_mem_iUnion_centreCutSiegelSetAmple_le
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ κ : ℝ) (hκ : 1 ≤ κ) (hc : 0 < c) (hd₁ : 0 < d₁)
    (T : Finset (AdelicGL2 (𝓞 F) F)) :
    ∃ N : ℕ, ∀ h : AdelicGL2 (𝓞 F) F,
      {γ : Matrix.GeneralLinearGroup (Fin 2) F |
          globalPoints (𝓞 F) F γ * h ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ}.Finite ∧
        {γ : Matrix.GeneralLinearGroup (Fin 2) F |
          globalPoints (𝓞 F) F γ * h ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ}.ncard ≤ N := by sorry
