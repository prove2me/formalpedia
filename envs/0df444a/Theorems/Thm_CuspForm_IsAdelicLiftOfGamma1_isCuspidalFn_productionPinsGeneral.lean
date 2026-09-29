-- Prove2me | Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_isCuspidalFn_productionPinsGeneral
-- name    : CuspForm.IsAdelicLiftOfGamma1.isCuspidalFn_productionPinsGeneral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/d113095a-e53d-5299-9944-ead6a6874579
-- title:
--   Cuspidality of the adelic lift of a weight-two cusp form
-- statement:
--   Fix a positive integer $M$, a cusp form $h$ of weight $2$ for $\Gamma_1(M)$, and a function $\Phi$ on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ (the general linear group of rank two over the adele ring of $\mathbb{Q}$) with complex values. The hypothesis is that $\Phi$ is an adelic lift of $h$ in the sense of [`CuspForm.IsAdelicLiftOfGamma1`](def/CuspForm_AdelicLiftGamma1.html#L14), i.e. the conjunction of three conditions: $\Phi(\gamma x) = \Phi(x)$ for every $\gamma \in \mathrm{GL}_2(\mathbb{Q})$ embedded adelically by `globalPoints` and every adelic $x$; $\Phi(x\,u) = \Phi(x)$ for every $u$ in the finite level-one subgroup at the ideal $M\mathcal{O}_{\mathbb{Q}}$, embedded into the adelic group by `finEmbed`; and, for every adelic $g$ whose finite part `glFin` is trivial and whose real component $\mathrm{ratArchGL2}(g)$ has positive determinant, $\Phi(g) = (h \mid_2 \mathrm{ratArchGL2}(g))(i)$. The conclusion is `IsCuspidalFn` for $\Phi$ with respect to the one-parameter unipotent family $x \mapsto \begin{pmatrix}1&x\\0&1\end{pmatrix}$ and to the measurable space and measure components `nS`, `ν` on $\mathbb{A}_{\mathbb{Q}}$ of the carrier pins `productionPinsGeneral ℚ` (those assembled by `productionPinsGeneralOf` from the Siegel-set parameters $1/2, 1, 1/2, 2$, the level subgroups `levelOne ⊓ finiteAdelicGL2Subgroup`, the Hecke generators `heckeGen`, and the adelic box of $\mathbb{Q}$): for every $g \in \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, the constant term of $\Phi$ at $g$ along that unipotent family, integrated over $\mathbb{A}_{\mathbb{Q}}$ against $\nu$, is zero.
--
--   This is the analytic step in the passage from a classical cusp form to a cuspidal automorphic form: the adelization of a weight-two cusp form on $\Gamma_1(M)$ has vanishing constant term along the standard unipotent subgroup, the integral reducing to the zeroth Fourier coefficient of $h$ at a cusp. It is used in [`CuspForm.IsEigenformWith.isIsotypicCuspFormAt_of_isAdelicLiftOfGamma1`](thm.html#CuspForm.IsEigenformWith.isIsotypicCuspFormAt_of_isAdelicLiftOfGamma1) to place the adelic lift of a Hecke eigenform in the cuspidal isotypic space attached to its eigensystem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsAdelicLiftOfGamma1_isCuspidalFn_productionPinsGeneral.lean

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

theorem CuspForm.IsAdelicLiftOfGamma1.isCuspidalFn_productionPinsGeneral
    {M : ℕ} [NeZero M] {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ) :
    @IsCuspidalFn _ (productionPinsGeneral ℚ).nS _ _ (productionPinsGeneral ℚ).ν unipotentGL2 Φ := by sorry
