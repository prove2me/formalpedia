-- Prove2me | Theorems.Thm_AutomorphicForm_apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero
-- name    : AutomorphicForm.apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/644a55dd-72f6-59e2-853d-b79a02857e5d
-- title:
--   Vanishing of the six complex flow derivatives forces SL₂(ℂ)-invariance
-- statement:
--   Let $F$ be a number field, $w$ an infinite place of $F$ with `hw : w.IsComplex`, and let $\varphi$ be a complex-valued function on `AdelicGL2 (𝓞 F) F`, the group of invertible $2\times 2$ matrices over the adele ring of $F$. Two hypotheses are imposed on $\varphi$. First, `IsArchSmoothAtComplex hw φ`: for every adelic $g$, the function sending a matrix $e : \mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to \mathbb{C}$ to $\varphi(g \cdot \mathrm{archComplexLiftAt}\,hw\,e)$ is $C^\infty$ in the real sense on the open set where $\det e \neq 0$, where `archComplexLiftAt` places an invertible $e$ at $w$ by transporting it along the entrywise isomorphism $\mathbb{C} \cong F_w$ and embedding $\mathrm{GL}_2(F_w)$ into the adelic group (and returns $1$ when $\det e = 0$). Second, for each of the six directions $d$ in `ArchDirComplex` ($H$, $E$, $F^-$, $iH$, $iE$, $iF^-$), the derivative at $t = 0$ of $t \mapsto \varphi(g \cdot \mathrm{archFlowAtComplex}\,hw\,d\,t)$ vanishes for all $g$, where the flow is the one-parameter matrix family `archFlowMatrixComplex d t` placed at $w$. The conclusion: for every adelic $g$ and every $h \in \mathrm{GL}_2(\mathbb{C})$ whose determinant, as a unit of $\mathbb{C}$, equals $1$, one has $\varphi(g \cdot \mathrm{archComplexGLAt}\,hw\,h) = \varphi(g)$.
--
--   This is the statement that a function smooth at a complex place and annihilated by the Lie algebra of $\mathrm{SL}_2(\mathbb{C})$ acting at that place is invariant under the whole group $\mathrm{SL}_2(\mathbb{C})$ placed at $w$, the complex-place counterpart of the corresponding real-place result. It is used in the analysis of cuspidal constituents at a complex place, where it isolates the degenerate case in which the infinitesimal action is trivial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ)
    (hD : ∀ d : ArchDirComplex, archDerivAtComplex hw d φ = 0)
    (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℂ) (hh : Matrix.GeneralLinearGroup.det h = 1) :
    φ (g * archComplexGLAt hw h) = φ g := by sorry
