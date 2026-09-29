-- Prove2me | Theorems.Thm_AutomorphicForm_isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport
-- name    : AutomorphicForm.isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/0e9cd4af-b586-599f-8d93-66a05c50d6dc
-- title:
--   Right convolution preserves smooth compactly supported archimedean factors
-- statement:
--   Let $F$ be a number field, and equip $G = \mathrm{GL}_2(\mathbb{A}_{F,\infty})$, the group of invertible $2\times 2$ matrices over the infinite adele ring of $F$, with a measurable space structure that is Borel for its topology; let $\mu$ be a Haar measure on $G$. Let $f_\infty, g \colon G \to \mathbb{C}$ be functions such that: $f_\infty$ satisfies `IsArchTestFactor`, that is, there is a function $\Phi$ on $2\times 2$ matrices over the mixed space $\mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$ of $F$ which is $C^\infty$ in the real sense (`ContDiff ℝ ⊤`) with $f_\infty(h) = \Phi(\mathrm{archEntries}\,h)$ for all $h \in G$, where $\mathrm{archEntries}\,h$ is the matrix of entries of $h$ transported along the ring isomorphism from $\mathbb{A}_{F,\infty}$ to the mixed space, and moreover $f_\infty$ has compact support; and $g$ is continuous with compact support. Then the function $x \mapsto \int_G f_\infty(xa)\,g(a)\,d\mu(a)$ again satisfies `IsArchTestFactor`: it is of the form (smooth function of the mixed-space matrix entries) composed with $\mathrm{archEntries}$, and has compact support.
--
--   This is the archimedean half of the statement that a convolution of factorizable test functions on $\mathrm{GL}_2(\mathbb{A}_F)$ is again factorizable, the case $g(a) = f'_\infty(a^{-1})$ giving right convolution by a second test factor. It is used in the construction of a factorizable test function with prescribed archimedean behaviour attached to a cuspidal constituent, in [`AutomorphicForm.CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_rightConv_comp_inv`](thm.html#AutomorphicForm.CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_rightConv_comp_inv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport.lean

import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField MeasureTheory AutomorphicForm

theorem AutomorphicForm.isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing F))] [BorelSpace (GL (Fin 2) (InfiniteAdeleRing F))]
    (μ : Measure (GL (Fin 2) (InfiniteAdeleRing F))) [μ.IsHaarMeasure]
    (fa g : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hfa : IsArchTestFactor F fa) (hg : Continuous g) (hgs : HasCompactSupport g) :
    IsArchTestFactor F (fun x => ∫ a, fa (x * a) * g a ∂μ) := by sorry
