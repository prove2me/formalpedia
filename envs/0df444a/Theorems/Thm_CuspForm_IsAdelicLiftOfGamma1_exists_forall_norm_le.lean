-- Prove2me | Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_exists_forall_norm_le
-- name    : CuspForm.IsAdelicLiftOfGamma1.exists_forall_norm_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/3bd1a271-df7f-5a02-823f-7a23c38f2135
-- title:
--   Boundedness of the adelic lift of a weight-two cusp form
-- statement:
--   Let $M$ be a natural number that is nonzero, let $h$ be a cusp form of weight $2$ for the congruence subgroup $\Gamma_1(M)$, and let $\Phi$ be a complex-valued function on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, the group of units of $2\times 2$ matrices over the adele ring of $\mathbb{Q}$. Assume $\Phi$ is an adelic lift of $h$ in the sense of [`CuspForm.IsAdelicLiftOfGamma1`](def/CuspForm_AdelicLiftGamma1.html#L14), that is: (i) $\Phi(\gamma x) = \Phi(x)$ for every $\gamma \in \mathrm{GL}_2(\mathbb{Q})$, embedded adelically by [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15), and every adelic $x$; (ii) $\Phi(x u) = \Phi(x)$ for every $u$ in the subgroup [`NumberField.AdelicLevel.finiteLevelOne`](def/NumberField_AdelicLevel.html#L418) at the ideal $(M)$ of $\mathcal{O}_{\mathbb{Q}}$ — the elements $u$ of $\mathrm{GL}_2$ over the finite adeles for which both $u$ and $u^{-1}$ satisfy the predicate `IsLevelOneMatrix` at that ideal — pushed into the full adelic group by [`AdelicDock.finEmbed`](def/AdelicDock_LocalEmbedding.html#L145); and (iii) for every adelic $g$ whose finite component `glFin` is trivial and whose real matrix [`LanglandsTunnell.ratArchGL2 g`](def/LanglandsTunnell_DeltaLift.html#L16), obtained from the archimedean component at the infinite place of $\mathbb{Q}$, has positive determinant, one has $\Phi(g) = (h \mid_{2} \mathrm{ratArchGL2}\,g)(i)$, the weight-$2$ slash action of that real matrix on $h$ evaluated at the point $i$ of the upper half-plane. The conclusion is that there exists a real constant $C$ such that $\|\Phi(g)\| \le C$ for all $g \in \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$.
--
--   This is the classical statement that the adelic lift of a weight-two cusp form is a bounded function on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, obtained from the boundedness of $y\,|h(x+iy)|$ on the upper half-plane together with the decomposition of an adelic matrix into a rational point times a level-one element supplied by [`NumberField.AdelicLevel.exists_globalPoints_mul_mem_levelOne_rat`](thm.html#NumberField.AdelicLevel.exists_globalPoints_mul_mem_levelOne_rat). It feeds the packaging of the lift as a bounded, cuspidal automorphic function, used in [`CuspForm.IsAdelicLiftOfGamma1.isBoundedGenuineFn_productionPinsGeneral_stdAddChar`](thm.html#CuspForm.IsAdelicLiftOfGamma1.isBoundedGenuineFn_productionPinsGeneral_stdAddChar) and [`CuspForm.IsAdelicLiftOfGamma1.isCuspidalFn_productionPinsGeneral`](thm.html#CuspForm.IsAdelicLiftOfGamma1.isCuspidalFn_productionPinsGeneral).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsAdelicLiftOfGamma1_exists_forall_norm_le.lean

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ModularForm

theorem CuspForm.IsAdelicLiftOfGamma1.exists_forall_norm_le
    {M : ℕ} [NeZero M] {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ) :
    ∃ C : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, ‖Φ g‖ ≤ C := by sorry
