-- Prove2me | Theorems.Thm_AutomorphicForm_exists_ne_zero_apply_mul_archRealGLAt_J_eq_mul_lower_of_finiteDimensional_of_forall_mem
-- name    : AutomorphicForm.exists_ne_zero_apply_mul_archRealGLAt_J_eq_mul_lower_of_finiteDimensional_of_forall_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/da2a0451-8d04-57c6-ac97-b5e16b9e17a0
-- title:
--   A J-rigid vector in weight-one Casimir eigenspaces
-- statement:
--   Let $F$ be a number field, $w$ an infinite place of $F$ with $hw : w.\mathrm{IsReal}$, and write $G =$ `AdelicGL2 (𝓞 F) F`, the group $\mathrm{GL}_2$ over the adele ring of $F$; for a real matrix group element $j \in \mathrm{GL}_2(\mathbb R)$ let $j_w =$ `archRealGLAt hw j` denote its image in $G$ under the inclusion of $\mathrm{GL}_2$ of the completion at $w$, transported along the isomorphism `ringEquivRealOfIsReal hw` of $F_w$ with $\mathbb R$. Let $\lambda \in \mathbb C$ with $\lambda \neq 1/4$, and let $S$ be a $\mathbb C$-submodule of the space of functions $G \to \mathbb C$ which is finite-dimensional over $\mathbb C$ and nonzero, such that: every $x \in S$ is smooth at $w$ in the sense of `IsArchSmoothAt hw`, i.e. for each $g \in G$ the function $e \mapsto x(g \cdot \mathrm{archRealLiftAt}\,hw\,e)$ on $2\times 2$ real matrices is $C^\infty$ on the locus $\det(e) \neq 0$; every $x \in S$ satisfies the predicate `HasArchCharacterAt₀ F w χ`, the transformation law at $w$ under the row-isometry subgroup for the character $\chi$ obtained by composing the weight-one character `archWeightCharℝ 1` with the transport map `rowIsometrySubgroup₀Map` along `ringEquivRealOfIsReal hw`; every $x \in S$ is a Casimir eigenfunction, $\mathrm{archCasimirAt}\,hw\,x = \lambda\, x$, where $\mathrm{archCasimirAt}$ is $-\bigl(\tfrac14 D_H D_H - \tfrac12 D_H + D_E D_{F^-}\bigr)$ in the directional derivatives $D_d x (g) = \frac{d}{dt}\big|_{t=0} x(g\cdot \mathrm{archFlowAt}\,hw\,d\,t)$ for $d \in \{H, E, F^-\}$; and $S$ is stable under $x \mapsto \bigl(g \mapsto (Lx)(g\,J_w)\bigr)$, where $L x = D_H x - i\,(D_E x + D_{F^-} x)$ and $J$ is the involution `UpperHalfPlane.J` of $\mathrm{GL}_2(\mathbb R)$. Then there exist $\psi \in S$ with $\psi \neq 0$ and a constant $c_J \in \mathbb C$ such that $\psi(g\,J_w) = c_J\,(L\psi)(g)$ for all $g \in G$.
--
--   This is the archimedean $(\mathfrak g, K)$-module step which, for a weight-one vector with Casimir eigenvalue different from $1/4$, converts the right translate by $J$ into a multiple of the lowering operator, so that the space is rigid under $J$. It is used in the construction of the archimedean parameter of a cuspidal constituent, via [`AutomorphicForm.archOccursInClassOf_archWeightChar_one_apply_mul_archRealGLAt_J_eq_mul_lower_of_ne_of_coversModCentre_rat`](thm.html#AutomorphicForm.archOccursInClassOf_archWeightChar_one_apply_mul_archRealGLAt_J_eq_mul_lower_of_ne_of_coversModCentre_rat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_ne_zero_apply_mul_archRealGLAt_J_eq_mul_lower_of_finiteDimensional_of_forall_mem.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open LanglandsTunnell LanglandsTunnell.RealArchParam
open LanglandsTunnell.Converse

open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.exists_ne_zero_apply_mul_archRealGLAt_J_eq_mul_lower_of_finiteDimensional_of_forall_mem
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal) (lam : ℂ) (hlam : lam ≠ 1 / 4)
    (S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) [FiniteDimensional ℂ S] (hS : S ≠ ⊥)
    (hsm : ∀ x ∈ S, IsArchSmoothAt hw x)
    (htype : ∀ x ∈ S, HasArchCharacterAt₀ F w ((archWeightCharℝ 1).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) x)
    (hΩ : ∀ x ∈ S, archCasimirAt hw x = lam • x)
    (hstab : ∀ x ∈ S,
      (fun g => (archDerivAt hw ArchDir.H x - Complex.I • (archDerivAt hw ArchDir.E x + archDerivAt hw ArchDir.Fm x)) (g * archRealGLAt hw UpperHalfPlane.J)) ∈ S) :
    ∃ ψ ∈ S, ψ ≠ 0 ∧ ∃ cJ : ℂ, ∀ g : AdelicGL2 (𝓞 F) F,
      ψ (g * archRealGLAt hw UpperHalfPlane.J) = cJ * (archDerivAt hw ArchDir.H ψ - Complex.I • (archDerivAt hw ArchDir.E ψ + archDerivAt hw ArchDir.Fm ψ)) g := by sorry
