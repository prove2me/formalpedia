-- Prove2me | Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_isKfSmooth
-- name    : CuspForm.IsAdelicLiftOfGamma1.isKfSmooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/2ddd6260-d145-5430-a7c5-1a76ea7699b6
-- title:
--   K_f-smoothness of adelic lifts of weight-two cusp forms
-- statement:
--   Let $M$ be a natural number with $M \neq 0$, let $h$ be a cusp form of weight $2$ for $\Gamma_1(M)$, and let $\Phi : \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ be a function on the adelic points of $\mathrm{GL}_2$ over $\mathbb{Q}$ (with $\mathbb{A}_{\mathbb{Q}}$ the adele ring of $\mathcal{O}_{\mathbb{Q}}$, $\mathbb{Q}$). Assume $\Phi$ is an adelic lift of $h$ in the sense of the predicate [`CuspForm.IsAdelicLiftOfGamma1`](def/CuspForm_AdelicLiftGamma1.html#L14), that is: $\Phi(\gamma x) = \Phi(x)$ for every $\gamma \in \mathrm{GL}_2(\mathbb{Q})$, embedded adelically, and every $x$; $\Phi(x \cdot u) = \Phi(x)$ for every $x$ and every $u$ in the level-one congruence subgroup `finiteLevelOne` at the ideal $M\mathcal{O}_{\mathbb{Q}}$ of $\mathrm{GL}_2$ of the finite adeles, transported to the adelic group by [`AdelicDock.finEmbed`](def/AdelicDock_LocalEmbedding.html#L145); and, for every adelic $g$ whose finite component is trivial and whose real component lies in $\mathrm{GL}_2^{+}(\mathbb{R})$, $\Phi(g)$ equals the weight-$2$ slash $(h \mid_2 g_\infty)$ evaluated at $i$. The conclusion is `IsKfSmooth ℚ Φ`: viewing $\Phi$ as a vector for the right-translation action, its stabiliser inside the subgroup of adelic matrices with trivial archimedean component (the kernel of `glArch`) is an open subset of that subgroup.
--
--   This is the smoothness, or local constancy at the finite places, of the adelisation of a classical weight-two form: the stabiliser contains the level subgroup attached to $M$. It feeds the later identification of such a lift as an isotypic cuspidal vector and the boundedness statement for the associated genuine function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsAdelicLiftOfGamma1_isKfSmooth.lean

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

theorem CuspForm.IsAdelicLiftOfGamma1.isKfSmooth
    {M : ℕ} [NeZero M] {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ) :
    IsKfSmooth ℚ Φ := by sorry
