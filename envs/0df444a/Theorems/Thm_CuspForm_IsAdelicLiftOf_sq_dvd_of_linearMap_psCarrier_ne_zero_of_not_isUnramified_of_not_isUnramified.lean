-- Prove2me | Theorems.Thm_CuspForm_IsAdelicLiftOf_sq_dvd_of_linearMap_psCarrier_ne_zero_of_not_isUnramified_of_not_isUnramified
-- name    : CuspForm.IsAdelicLiftOf.sq_dvd_of_linearMap_psCarrier_ne_zero_of_not_isUnramified_of_not_isUnramified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/97a17cc9-ab07-538e-85c7-8e4a7aa28ef9
-- title:
--   Both characters ramified at q forces q² ∣ M
-- statement:
--   Fix a natural number $M$ with $M \neq 0$, a cusp form $g$ of weight $2$ for $\Gamma_0(M)$, a prime $q$, and a function $\Phi$ on $\mathrm{GL}_2$ of the adele ring of $\mathbb{Q}$ with values in $\mathbb{C}$. Assume $g$ is an adelic lift of $\Phi$ in the sense of `IsAdelicLiftOf`, i.e. $\Phi$ is left invariant under the image of $\mathrm{GL}_2(\mathbb{Q})$ under [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15), right invariant under the image under [`AdelicDock.finEmbed`](def/AdelicDock_LocalEmbedding.html#L145) of the level-one subgroup attached to the ideal $(M)$ of $\mathcal{O}_{\mathbb{Q}}$, and, for every adelic $h$ whose finite component `glFin` is $1$ and whose real component `ratArchGL2` has positive determinant, satisfies $\Phi(h) = (g \mid[2] \mathrm{ratArchGL2}\,h)(i)$. Let $\mu_1, \mu_2 \colon \mathbb{Q}_q^\times \to \mathbb{C}^\times$ be group homomorphisms, and let $f$ be a $\mathbb{C}$-linear map from [`LocalNewvector.AdelicSpan`](def/LocalNewvector_AdelicSpanCarrier.html#L82) $\Phi$, the span of the adelic translates $g \cdot \Phi$, to the principal-series space `PSCarrier` $q\,\mu_1\,\mu_2$ of locally constant functions $\varphi$ on $\mathrm{GL}_2(\mathbb{Q}_q)$ with $\varphi(b(a_1,a_2,x)\,g) = \mu_1(a_1)\mu_2(a_2)\,\delta^{1/2}(a_1,a_2)\,\varphi(g)$ for Borel elements. Assume $f(x \cdot v) = x \cdot f(v)$ for all $x \in \mathrm{GL}_2(\mathbb{Q}_q)$ and all $v$, that $f \neq 0$, and that neither $\mu_1$ nor $\mu_2$ is unramified, i.e. each is nontrivial on some unit of norm $1$. Then $q^2$ divides $M$.
--
--   This is the local-conductor bound in the form needed here: a nonzero equivariant map from the local span of an adelic lift of a form of level $M$ into a principal series whose two characters are both ramified at $q$ can only exist when $q^2 \mid M$, the Atkin–Lehner–Casselman newvector constraint. It is used in the analysis of the characteristic polynomial of inertia at $q$ attached to a newform, via [`CuspForm.IsNewform.exists_charpoly_inertia_eq_and_pow_eq_one_iff_of_linearMap_psCarrier_ne_zero_of_isUnramified_ratio`](thm.html#CuspForm.IsNewform.exists_charpoly_inertia_eq_and_pow_eq_one_iff_of_linearMap_psCarrier_ne_zero_of_isUnramified_ratio), and rests on the vanishing of the $K_1(q^0)$-fixed vectors in such a principal series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsAdelicLiftOf_sq_dvd_of_linearMap_psCarrier_ne_zero_of_not_isUnramified_of_not_isUnramified.lean

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Definitions.Def_LocalNewvector_CharConductor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.IsAdelicLiftOf.sq_dvd_of_linearMap_psCarrier_ne_zero_of_not_isUnramified_of_not_isUnramified
    {M : ℕ} [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (q : ℕ) [Fact q.Prime]
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (_hlift : g.IsAdelicLiftOf Φ)
    (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ) (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂)
    (_hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v) (_hf0 : f ≠ 0)
    (_hμ₁ : ¬ LocalNewvector.IsUnramified q μ₁) (_hμ₂ : ¬ LocalNewvector.IsUnramified q μ₂) :
    q ^ 2 ∣ M := by sorry
