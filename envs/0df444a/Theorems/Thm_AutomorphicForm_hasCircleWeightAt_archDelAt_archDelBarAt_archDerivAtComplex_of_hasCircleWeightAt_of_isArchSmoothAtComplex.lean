-- Prove2me | Theorems.Thm_AutomorphicForm_hasCircleWeightAt_archDelAt_archDelBarAt_archDerivAtComplex_of_hasCircleWeightAt_of_isArchSmoothAtComplex
-- name    : AutomorphicForm.hasCircleWeightAt_archDelAt_archDelBarAt_archDerivAtComplex_of_hasCircleWeightAt_of_isArchSmoothAtComplex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/c92bbf21-6216-5984-898f-a62a0b1596b3
-- title:
--   Circle-weight shifts of partial, partial̄ and H at a complex place
-- statement:
--   Let $K$ be a number field, $w$ an infinite place of $K$ with $hw : w.\mathrm{IsComplex}$, and $n$ an integer. Let $\psi$ be a complex-valued function on the adelic group $\mathrm{GL}_2(\mathbb{A}_K)$, realised as `AdelicGL2 (𝓞 K) K`, subject to two hypotheses. First, `IsArchSmoothAtComplex hw ψ`: for every $g$ the function $e \mapsto \psi(g \cdot \mathrm{archComplexLiftAt}\,hw\,e)$ on $2\times 2$ complex matrices is $C^\infty$ in the real sense on the open set where $\det e \neq 0$, the lift placing $e$ in the $w$-component. Second, `HasCircleWeightAt hw n ψ`: for every unit $\zeta$ of $\mathbb{C}$ with $\lVert\zeta\rVert = 1$ and every $g$, $\psi(g \cdot \mathrm{archCircleAt}\,hw\,\zeta) = \zeta^{n}\,\psi(g)$, where $\mathrm{archCircleAt}$ inserts the matrix $\mathrm{circleGL2}\,\zeta$ at $w$. Here $\mathrm{archDerivAtComplex}\,hw\,d\,\psi$ is the derivative at $t=0$ of $t \mapsto \psi(g\cdot \mathrm{archFlowAtComplex}\,hw\,d\,t)$ along the one-parameter flow in direction $d$ at $w$, and for $d \in \{H,E,F\}$ one sets $\mathrm{archDelAt}\,hw\,d = \tfrac12(\partial_d - i\,\partial_{id})$ and $\mathrm{archDelBarAt}\,hw\,d = \tfrac12(\partial_d + i\,\partial_{id})$ in terms of the paired real directions. The conclusion is the sixfold conjunction: $\mathrm{archDelAt}\,hw\,E\,\psi$ has circle weight $n+2$ at $w$, $\mathrm{archDelBarAt}\,hw\,E\,\psi$ weight $n-2$, $\mathrm{archDelAt}\,hw\,F\,\psi$ weight $n-2$, $\mathrm{archDelBarAt}\,hw\,F\,\psi$ weight $n+2$, and both $\mathrm{archDerivAtComplex}\,hw\,H\,\psi$ and $\mathrm{archDerivAtComplex}\,hw\,(iH)\,\psi$ weight $n$.
--
--   This is the weight bookkeeping for the raising and lowering operators at a complex place: the holomorphic and antiholomorphic derivations along $E$ and $F$ shift the circle weight by $\pm 2$, while the two real directions spanning the Cartan direction preserve it. It is used in the estimate [`AutomorphicForm.exists_forall_eLpNorm_archDerivAtComplex_iH_and_E_sub_Fm_and_iE_add_iFm_foldr_le_of_mem_archCutSubmodule`](thm.html#AutomorphicForm.exists_forall_eLpNorm_archDerivAtComplex_iH_and_E_sub_Fm_and_iE_add_iFm_foldr_le_of_mem_archCutSubmodule), where weight-graded pieces of archimedean derivatives are controlled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_hasCircleWeightAt_archDelAt_archDelBarAt_archDerivAtComplex_of_hasCircleWeightAt_of_isArchSmoothAtComplex.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.hasCircleWeightAt_archDelAt_archDelBarAt_archDerivAtComplex_of_hasCircleWeightAt_of_isArchSmoothAtComplex
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex) (n : ℤ)
    (ψ : AdelicGL2 (𝓞 K) K → ℂ) (hψ : IsArchSmoothAtComplex hw ψ)
    (hwt : HasCircleWeightAt hw n ψ) :
    HasCircleWeightAt hw (n + 2) (archDelAt hw .E ψ) ∧
      HasCircleWeightAt hw (n - 2) (archDelBarAt hw .E ψ) ∧
      HasCircleWeightAt hw (n - 2) (archDelAt hw .Fm ψ) ∧
      HasCircleWeightAt hw (n + 2) (archDelBarAt hw .Fm ψ) ∧
      HasCircleWeightAt hw n (archDerivAtComplex hw .H ψ) ∧
      HasCircleWeightAt hw n (archDerivAtComplex hw .iH ψ) := by sorry
