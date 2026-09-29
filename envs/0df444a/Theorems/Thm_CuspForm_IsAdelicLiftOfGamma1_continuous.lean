-- Prove2me | Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_continuous
-- name    : CuspForm.IsAdelicLiftOfGamma1.continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/12574ab0-a570-50df-9040-4ac059aa23a2
-- title:
--   Continuity of the adelic lift of a weight-two Γ₁(M) cusp form
-- statement:
--   Let $M$ be a natural number with $M \neq 0$, let $h$ be a cusp form of weight $2$ for the congruence subgroup $\Gamma_1(M)$, and let $\Phi \colon \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ be a function on the group of invertible $2 \times 2$ matrices over the adele ring of $\mathbb{Q}$ (relative to $\mathcal{O}_{\mathbb{Q}}$). Assume that $\Phi$ is an adelic lift of $h$ in the sense of [`CuspForm.IsAdelicLiftOfGamma1`](def/CuspForm_AdelicLiftGamma1.html#L14), that is: (i) $\Phi(\gamma x) = \Phi(x)$ for every $\gamma \in \mathrm{GL}_2(\mathbb{Q})$, embedded into $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ entrywise by the structure map, and every adelic $x$; (ii) $\Phi(x u) = \Phi(x)$ for every $x$ and every $u$ in the image under [`AdelicDock.finEmbed`](def/AdelicDock_LocalEmbedding.html#L145) of the subgroup `finiteLevelOne` of $\mathrm{GL}_2$ over the finite adeles attached to the ideal $N = (M) \subseteq \mathcal{O}_{\mathbb{Q}}$, namely the matrices $u$ for which both $u$ and $u^{-1}$ satisfy the level-one congruence condition `IsLevelOneMatrix` at $N$; and (iii) for every adelic $g$ whose finite component `glFin` is the identity and whose real archimedean component $\mathrm{ratArchGL2}(g) \in \mathrm{GL}_2(\mathbb{R})$ has positive determinant, $\Phi(g) = (h \mid_2 \mathrm{ratArchGL2}(g))(i)$, the weight-two slash action of that real matrix on $h$, evaluated at $i$ in the upper half-plane. The conclusion is that $\Phi$ is continuous.
--
--   This is the continuity clause in the passage from a classical weight-two cusp form on $\Gamma_1(M)$ to the corresponding automorphic function on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ (the adelization of a modular form). It is used by the cuspidality and boundedness statements for the lift and, through them, by the construction identifying the lift of a Hecke eigenform as an isotypic cusp form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsAdelicLiftOfGamma1_continuous.lean

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

theorem CuspForm.IsAdelicLiftOfGamma1.continuous
    {M : ℕ} [NeZero M] {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ) :
    Continuous Φ := by sorry
