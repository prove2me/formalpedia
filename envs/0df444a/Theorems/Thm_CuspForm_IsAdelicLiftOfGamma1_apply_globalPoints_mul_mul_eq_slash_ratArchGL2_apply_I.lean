-- Prove2me | Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_apply_globalPoints_mul_mul_eq_slash_ratArchGL2_apply_I
-- name    : CuspForm.IsAdelicLiftOfGamma1.apply_globalPoints_mul_mul_eq_slash_ratArchGL2_apply_I
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/f9e342bc-c62e-5840-b597-80a9017b7611
-- title:
--   Adelic lift of a Γ₁(M) cusp form on γ x u
-- statement:
--   Let $M$ be a positive integer, let $h$ be a cusp form of weight $2$ for $\Gamma_1(M)$, and let $\Phi \colon \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ satisfy [`CuspForm.IsAdelicLiftOfGamma1 h Φ`](def/CuspForm_AdelicLiftGamma1.html#L14), i.e. (i) $\Phi(\iota(\gamma) g) = \Phi(g)$ for all $\gamma \in \mathrm{GL}_2(\mathbb{Q})$ and all adelic $g$, where $\iota$ is the map `globalPoints` induced by $\mathbb{Q} \to \mathbb{A}_{\mathbb{Q}}$; (ii) $\Phi(g \cdot \mathrm{finEmbed}(u_0)) = \Phi(g)$ for every $u_0$ in the subgroup `finiteLevelOne` at the ideal $\mathrm{ratLevel}(M) = (M) \subseteq \mathcal{O}_{\mathbb{Q}}$ (both $u_0$ and $u_0^{-1}$ satisfying `IsLevelOneMatrix` at that ideal), $\mathrm{finEmbed}$ being the embedding of the finite-adelic $\mathrm{GL}_2$ into the adelic one by zero-extension at the infinite places; and (iii) $\Phi(g) = (h \mid_2 \mathrm{ratArchGL2}(g))(i)$ whenever the finite part $\mathrm{glFin}(g)$ is $1$ and the real matrix $\mathrm{ratArchGL2}(g)$ — the component of $g$ at the unique infinite place of $\mathbb{Q}$, transported to $\mathrm{GL}_2(\mathbb{R})$ — has positive determinant. Then for $\gamma \in \mathrm{GL}_2(\mathbb{Q})$, for $x$ with $\mathrm{glFin}(x) = 1$ and $\mathrm{ratArchGL2}(x) \in \mathrm{GL}_2^+(\mathbb{R})$, and for $u$ in the level subgroup $U(\mathrm{ratLevel}(M))$ of `productionPinsGeneral ℚ` (the intersection of `levelOne` at $(M)$ with `finiteAdelicGL2Subgroup`, i.e. finite part of level $M$ and archimedean part trivial), one has $\Phi(\iota(\gamma) \, x \, u) = (h \mid_2 \mathrm{ratArchGL2}(x))(i)$, the weight-$2$ slash action evaluated at the point $i$ of the upper half-plane.
--
--   This is the evaluation rule for the adelisation of a weight-two cusp form on a product decomposition $\gamma \cdot x_\infty \cdot u$ of the kind furnished by strong approximation for $\mathrm{GL}_2$ over $\mathbb{Q}$: the three defining invariances of an adelic lift determine its value on such a product in terms of the classical form. It is used in the construction of the adelic automorphic form attached to a classical cusp form, in particular by [`CuspForm.IsAdelicLiftOfGamma1.exists_forall_apply_unipotentGL2_add_ratArchLine_mul_eq_slash_apply_I`](thm.html#CuspForm.IsAdelicLiftOfGamma1.exists_forall_apply_unipotentGL2_add_ratArchLine_mul_eq_slash_apply_I).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsAdelicLiftOfGamma1_apply_globalPoints_mul_mul_eq_slash_ratArchGL2_apply_I.lean

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

theorem CuspForm.IsAdelicLiftOfGamma1.apply_globalPoints_mul_mul_eq_slash_ratArchGL2_apply_I
    {M : ℕ} [NeZero M] {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ)
    (γ : GL (Fin 2) ℚ) (x u : AdelicGL2 (𝓞 ℚ) ℚ)
    (hu : u ∈ (productionPinsGeneral ℚ).U (AdelicDock.ratLevel M))
    (hx : glFin (𝓞 ℚ) ℚ x = 1) (hpos : LanglandsTunnell.ratArchGL2 x ∈ Matrix.GLPos (Fin 2) ℝ) :
    Φ (globalPoints (𝓞 ℚ) ℚ γ * x * u) =
      ((⇑h) ∣[(2 : ℤ)] LanglandsTunnell.ratArchGL2 x) UpperHalfPlane.I := by sorry
