-- Prove2me | Theorems.Thm_AutomorphicForm_IsFactorizableTestFn_isArchSmoothAt_and_archDerivAt_eq_tensor
-- name    : AutomorphicForm.IsFactorizableTestFn.isArchSmoothAt_and_archDerivAt_eq_tensor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/5189fd3b-c1cd-58e5-8bed-6123b56933fc
-- title:
--   Factorisable test functions are smooth and differentiable at a real place
-- statement:
--   Let $K$ be a number field, let $w$ be an infinite place of $K$ with $w$ real (witnessed by `hw`), and let $\alpha \colon \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be a function on the adelic general linear group that is a factorisable test function: there are $f_\infty$ on $\mathrm{GL}_2$ of the infinite adele ring and $f_{\mathrm{fin}}$ on $\mathrm{GL}_2$ of the finite adele ring of $\mathcal{O}_K$ in $K$ such that $f_\infty$ is of the form $\Phi \circ \mathrm{archEntries}$ for some $\Phi$ of class $C^\infty$ over $\mathbb{R}$ on matrices with entries in the mixed space $\mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$ and has compact support, $f_{\mathrm{fin}}$ is locally constant with compact support, and $\alpha(g) = f_\infty(\mathrm{glArch}\,g)\, f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ for all $g$, where `glArch` and `glFin` are the maps induced on $\mathrm{GL}_2$ by the two projections of the adele ring. Then two things hold. First, $\alpha$ satisfies `IsArchSmoothAt hw`: for every $g \in \mathrm{GL}_2(\mathbb{A}_K)$ the function $e \mapsto \alpha(g \cdot \mathrm{archRealLiftAt}\,hw\,e)$ of a real $2 \times 2$ matrix $e$, where $\mathrm{archRealLiftAt}$ places an invertible $e$ into the $w$-component and returns $1$ when $\det e = 0$, is $C^\infty$ over $\mathbb{R}$ on the set $\{e : \det e \neq 0\}$. Second, there exist an archimedean test factor $f_\infty$ and a finite test factor $f_{\mathrm{fin}}$ (in the above sense) with $\alpha(y) = f_\infty(\mathrm{glArch}\,y)\, f_{\mathrm{fin}}(\mathrm{glFin}\,y)$ for all $y$, and such that for each of the three directions $d \in \{H, E, F\}$ there is an archimedean test factor $f_\infty'$ with $(\mathrm{archDerivAt}\,hw\,d\,\alpha)(y) = f_\infty'(\mathrm{glArch}\,y)\, f_{\mathrm{fin}}(\mathrm{glFin}\,y)$ for all $y$, where $\mathrm{archDerivAt}\,hw\,d\,\alpha$ at $y$ is the derivative at $t = 0$ of $t \mapsto \alpha(y \cdot \mathrm{archFlowAt}\,hw\,d\,t)$, the flow being the one-parameter matrix group for the direction $d$ placed at $w$. In particular the finite factor is unchanged, and is the same for all three directions.
--
--   This is the closure statement underpinning the archimedean calculus of right convolution on $\mathrm{GL}_2(\mathbb{A}_K)$: a pure tensor test function is smooth in the real matrix entries at a real place, and each right-invariant derivative along $H$, $E$ or $F$ is again a pure tensor with the same locally constant finite factor. It is used by the results computing the action of the Casimir element at $w$ on right convolutions, where iterated derivatives must remain continuous, compactly supported and factorisable in order to move the Casimir operator across the convolution.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_IsFactorizableTestFn_isArchSmoothAt_and_archDerivAt_eq_tensor.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.IsFactorizableTestFn.isArchSmoothAt_and_archDerivAt_eq_tensor
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hα : IsFactorizableTestFn K α) :
    IsArchSmoothAt hw α ∧
    ∃ (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ),
      IsArchTestFactor K fa ∧ IsFinTestFactor K ff ∧
      (∀ y, α y = fa (glArch (𝓞 K) K y) * ff (glFin (𝓞 K) K y)) ∧
      ∀ d : ArchDir, ∃ fa' : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, IsArchTestFactor K fa' ∧
        ∀ y, archDerivAt hw d α y = fa' (glArch (𝓞 K) K y) * ff (glFin (𝓞 K) K y) := by sorry
