-- Prove2me | Theorems.Thm_CuspForm_IsAdelicLiftOfGamma1_apply_centralScalar_mul_eq_of_forall_snd_eq_one_of_archCoord_pos
-- name    : CuspForm.IsAdelicLiftOfGamma1.apply_centralScalar_mul_eq_of_forall_snd_eq_one_of_archCoord_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/82fc597e-15d0-5907-8e54-85f230cdd8bd
-- title:
--   Positive central scalars act trivially on the adelic lift
-- statement:
--   Let $M$ be a natural number, $h$ a cusp form of weight $2$ for $\Gamma_1(M)$, and $\Phi$ a complex-valued function on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ (the adele ring of $\mathbb{Q}$ formed with $\mathcal{O}_{\mathbb{Q}}$). Assume $\Phi$ satisfies the project's predicate [`CuspForm.IsAdelicLiftOfGamma1`](def/CuspForm_AdelicLiftGamma1.html#L14) for $h$, which is the conjunction of three conditions: $\Phi(\iota(\gamma)x)=\Phi(x)$ for all $\gamma\in\mathrm{GL}_2(\mathbb{Q})$ and all $x$, where $\iota$ is the map `globalPoints` induced by $\mathbb{Q}\to\mathbb{A}_{\mathbb{Q}}$; $\Phi(x\cdot u)=\Phi(x)$ for all $x$ and all $u$ in the image under [`AdelicDock.finEmbed`](def/AdelicDock_LocalEmbedding.html#L145) of the subgroup `finiteLevelOne` at the ideal $(M)$ of $\mathcal{O}_{\mathbb{Q}}$, that is, those $u\in\mathrm{GL}_2$ over the finite adeles for which both $u$ and $u^{-1}$ satisfy the project's predicate `IsLevelOneMatrix` at $(M)$; and $\Phi(y)=\bigl(h\mid_{2}\,\mathrm{ratArchGL2}(y)\bigr)(i)$ for every adelic $y$ whose finite part `glFin` is $1$ and whose real component $\mathrm{ratArchGL2}(y)$ lies in $\mathrm{GL}_2^{+}(\mathbb{R})$. Assume further $M\neq 0$; let $z$ be a unit of $\mathbb{A}_{\mathbb{Q}}$ whose component at every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ equals $1$, and whose archimedean coordinate [`RatIdele.archCoord`](def/RatIdele_Normalizer.html#L87) $z$ — the image of the component of $z$ at the infinite place of $\mathbb{Q}$ under the identification of that completion with $\mathbb{R}$ — is strictly positive. Then for every $x\in\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ one has $\Phi(\mathrm{diag}(z,z)\,x)=\Phi(x)$, where $\mathrm{diag}(z,z)$ is `centralScalar` applied to $z$.
--
--   This is the first step towards the central character of the adelic lift of a weight-two cusp form: the connected archimedean part of the centre of $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ acts trivially, so the central quasi-character is determined by the finite ideles. It is used in the construction of the finite-order Hecke character attached to the nebentypus of $h$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsAdelicLiftOfGamma1_apply_centralScalar_mul_eq_of_forall_snd_eq_one_of_archCoord_pos.lean

import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_RatIdele_Normalizer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm

theorem CuspForm.IsAdelicLiftOfGamma1.apply_centralScalar_mul_eq_of_forall_snd_eq_one_of_archCoord_pos
    {M : ℕ} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    {Φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hΦ : CuspForm.IsAdelicLiftOfGamma1 h Φ) (hM : M ≠ 0)
    (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hz : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), (z : AdeleRing (𝓞 ℚ) ℚ).2 v = 1)
    (hpos : 0 < RatIdele.archCoord z)
    (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    Φ (centralScalar (𝓞 ℚ) ℚ z * x) = Φ x := by sorry
