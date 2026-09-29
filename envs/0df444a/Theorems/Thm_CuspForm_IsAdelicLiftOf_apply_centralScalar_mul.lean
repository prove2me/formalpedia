-- Prove2me | Theorems.Thm_CuspForm_IsAdelicLiftOf_apply_centralScalar_mul
-- name    : CuspForm.IsAdelicLiftOf.apply_centralScalar_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/ad1563b0-13e3-52e3-9b0b-bedad11dc8a7
-- title:
--   Central invariance of an adelic lift of a weight-two form
-- statement:
--   Let $M$ be a non-zero natural number, let $g$ be a cusp form of weight $2$ for $\Gamma_0(M)$, and let $\Phi$ be a complex-valued function on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, where $\mathbb{A}_{\mathbb{Q}}$ is the adele ring of $\mathbb{Q}$ relative to $\mathcal{O}_{\mathbb{Q}}$. Assume that $\Phi$ is an adelic lift of $g$ in the sense of the predicate `IsAdelicLiftOf`, that is: (i) $\Phi(\gamma x) = \Phi(x)$ for every $\gamma \in \mathrm{GL}_2(\mathbb{Q})$, mapped into $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ by `globalPoints`, and every $x$; (ii) $\Phi(xu) = \Phi(x)$ for every $u$ in the subgroup `finiteLevelOne` of $\mathrm{GL}_2$ over the finite adeles attached to the ideal $(M)$ of $\mathcal{O}_{\mathbb{Q}}$ — those $u$ with both $u$ and $u^{-1}$ level-one matrices for that ideal — embedded by `finEmbed`, and every $x$; and (iii) for every $h \in \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ whose finite component `glFin` is trivial and whose real component `ratArchGL2` lies in $\mathrm{GL}_2^{+}(\mathbb{R})$, one has $\Phi(h) = (g \mid_2 \mathrm{ratArchGL2}(h))(i)$. Then for every idele $z \in \mathbb{A}_{\mathbb{Q}}^{\times}$ and every $x \in \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, $$\Phi\big((z \cdot 1)\, x\big) = \Phi(x),$$ where $z \cdot 1$ denotes the central scalar matrix `centralScalar` with entries $z$ on the diagonal.
--
--   This is the statement that the adelic lift of a weight-two cusp form of trivial nebentypus on $\Gamma_0(M)$ has trivial central character: the centre $\mathbb{A}_{\mathbb{Q}}^{\times}$ of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ acts trivially on $\Phi$. It is used in the packaging of such lifts as isotypic automorphic forms with trivial central character, and in the identification of the central elements acting on the associated two-dimensional representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsAdelicLiftOf_apply_centralScalar_mul.lean

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

theorem CuspForm.IsAdelicLiftOf.apply_centralScalar_mul
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : g.IsAdelicLiftOf Φ)
    (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    Φ (centralScalar (𝓞 ℚ) ℚ z * x) = Φ x := by sorry
