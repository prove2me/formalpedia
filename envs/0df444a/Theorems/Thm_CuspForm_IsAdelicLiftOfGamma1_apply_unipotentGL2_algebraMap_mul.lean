-- Prove2me | Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_apply_unipotentGL2_algebraMap_mul
-- name    : CuspForm.IsAdelicLiftOfGamma1.apply_unipotentGL2_algebraMap_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/9ba282a7-4a18-5f78-94f6-36f90699a2f8
-- title:
--   Adelic lifts are left-invariant under rational unipotents
-- statement:
--   Let $M$ be a natural number, let $h$ be a cusp form of weight $2$ for the congruence subgroup $\Gamma_1(M)$, and let $\Phi$ be a complex-valued function on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, the general linear group of degree $2$ over the adele ring of $\mathbb{Q}$ attached to $\mathcal{O}_{\mathbb{Q}}$. Assume $\Phi$ is an adelic lift of $h$ in the sense of the predicate [`CuspForm.IsAdelicLiftOfGamma1`](def/CuspForm_AdelicLiftGamma1.html#L14), i.e. the conjunction of: (i) $\Phi(\gamma x) = \Phi(x)$ for all $\gamma \in \mathrm{GL}_2(\mathbb{Q})$, pushed into $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ entrywise by the structure map, and all adelic $x$; (ii) $\Phi(xu) = \Phi(x)$ for every $u$ in the subgroup of $\mathrm{GL}_2$ of the finite adeles consisting of those $u$ such that both $u$ and $u^{-1}$ satisfy `IsLevelOneMatrix` for the ideal $(M)$ of $\mathcal{O}_{\mathbb{Q}}$, embedded into $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ by [`AdelicDock.finEmbed`](def/AdelicDock_LocalEmbedding.html#L145); and (iii) for every adelic $x$ whose finite part is trivial and whose real component `ratArchGL2` lies in $\mathrm{GL}_2^+(\mathbb{R})$, $\Phi(x)$ equals the weight-$2$ slash action of that real component on $h$ evaluated at $i$. The conclusion is that for every $\beta \in \mathbb{Q}$ and every $g \in \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ one has $\Phi(n(\beta)g) = \Phi(g)$, where $n(\beta)$ is the unit $\begin{pmatrix}1&\beta\\0&1\end{pmatrix}$ with inverse $\begin{pmatrix}1&-\beta\\0&1\end{pmatrix}$, formed over the adeles from the principal adele attached to $\beta$.
--
--   This is the special case of the left $\mathrm{GL}_2(\mathbb{Q})$-invariance clause in the definition of an adelic lift that is needed for rational upper unipotent matrices, written in the form in which the unipotent element occurs in Whittaker-type computations on the adelic group. It is used in the analysis of the Fourier expansion of the adelic lift along the standard additive character, in particular by [`CuspForm.IsAdelicLiftOfGamma1.isBoundedGenuineFn_productionPinsGeneral_stdAddChar`](thm.html#CuspForm.IsAdelicLiftOfGamma1.isBoundedGenuineFn_productionPinsGeneral_stdAddChar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsAdelicLiftOfGamma1_apply_unipotentGL2_algebraMap_mul.lean

import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicTraceProducer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField
open NumberField.AdelicBox NumberField.StandardAddChar AutomorphicForm

theorem CuspForm.IsAdelicLiftOfGamma1.apply_unipotentGL2_algebraMap_mul
    {M : ℕ} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ) (β : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    Φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * g) = Φ g := by sorry
