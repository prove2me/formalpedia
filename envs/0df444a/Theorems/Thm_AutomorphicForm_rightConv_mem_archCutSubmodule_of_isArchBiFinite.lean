-- Prove2me | Theorems.Thm_AutomorphicForm_rightConv_mem_archCutSubmodule_of_isArchBiFinite
-- name    : AutomorphicForm.rightConv_mem_archCutSubmodule_of_isArchBiFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/639938e3-30d1-58b8-b9b1-a8aacc8fe2c4
-- title:
--   Right convolution by an arch-bi-finite test function stays in the cut
-- statement:
--   Let $F$ be a number field and let $\mathrm{tys}$ be an archimedean type family for $F$: a function assigning to each infinite place $w$ of $F$ a natural number $\mathrm{card}\,w$ together with, for each $i < \mathrm{card}\,w$, a datum consisting of a natural number $n$ and a representation of the subgroup `rowIsometrySubgroup₀` of $\mathrm{GL}_2$ over the completion of $F$ at $w$ on $\mathbb{C}^n$. Let $g \colon \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be continuous, and let $\alpha \colon \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a factorizable test function, i.e. $\alpha(x) = f_\infty(\mathrm{glArch}\,x)\, f_{\mathrm{fin}}(\mathrm{glFin}\,x)$ for some $f_\infty$ on $\mathrm{GL}_2$ of the infinite adeles which is compactly supported and given by a $C^\infty$ function of the matrix entries under `archEntries`, and some compactly supported locally constant $f_{\mathrm{fin}}$ on $\mathrm{GL}_2$ of the finite adeles. Assume moreover that $\alpha$ is arch-bi-finite for $\mathrm{tys}$, meaning that $x \mapsto \alpha(x^{-1})$ lies in `archCutSubmodule F tys`, the intersection over all infinite places $w$ of the supremum of the submodules `typeSubmodule` attached to the inclusion `rowIsometryInclAt₀ F w` and to the listed representations at $w$, and that $\alpha$ itself lies in the corresponding submodule `archDualCutSubmodule F tys` built from the dual type submodules. Then the right convolution $\mathrm{rightConv}\,F\,g\,\alpha$, given by $x \mapsto \int g(xy)\,\alpha(y)\,dy$ against the Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb{A}_F)$ for its Borel structure, also lies in `archCutSubmodule F tys`.
--
--   This is the standard bookkeeping step on archimedean $K$-types: convolving an arbitrary continuous function on $\mathrm{GL}_2(\mathbb{A}_F)$ on the right by a test function whose archimedean left and right translates span types drawn from a fixed finite list produces a function whose types at each infinite place are again among those listed. It is used in the construction of cuspidal constituents, where projectors are built as right convolutions and their images must be kept inside the prescribed archimedean cut.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_rightConv_mem_archCutSubmodule_of_isArchBiFinite.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent
open scoped ENNReal

theorem AutomorphicForm.rightConv_mem_archCutSubmodule_of_isArchBiFinite
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    (g : AdelicGL2 (𝓞 F) F → ℂ) (hg : Continuous g)
    (α : AdelicGL2 (𝓞 F) F → ℂ) (hα : IsFactorizableTestFn F α) (hαt : IsArchBiFinite F tys α) :
    rightConv F g α ∈ archCutSubmodule F tys := by sorry
