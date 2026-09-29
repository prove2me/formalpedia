-- Prove2me | Theorems.Thm_CuspForm_IsAdelicLiftOf_isUnramified_mul_of_linearMap_psCarrier_ne_zero
-- name    : CuspForm.IsAdelicLiftOf.isUnramified_mul_of_linearMap_psCarrier_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/783a1dbc-663a-5dac-a364-88c739663e14
-- title:
--   Unramifiedness of the central character μ₁μ₂
-- statement:
--   Let $M$ be a nonzero natural number, $g$ a cusp form of weight $2$ for $\Gamma_0(M)$, and $q$ a prime. Let $\Phi$ be a complex-valued function on $\mathrm{GL}_2$ of the adele ring of $\mathbb{Q}$ which is an adelic lift of $g$ in the sense of [`CuspForm.IsAdelicLiftOf`](def/CuspForm_AdelicLift.html#L14), namely: $\Phi$ is invariant under left translation by the image of $\mathrm{GL}_2(\mathbb{Q})$ under [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15); $\Phi$ is invariant under right translation by the image under [`AdelicDock.finEmbed`](def/AdelicDock_LocalEmbedding.html#L145) of the subgroup [`NumberField.AdelicLevel.finiteLevelOne`](def/NumberField_AdelicLevel.html#L418) attached to the ideal $(M)$ of $\mathcal{O}_{\mathbb{Q}}$; and for every adelic matrix $h$ whose finite part [`NumberField.AdelicLevel.glFin`](def/NumberField_AdelicLevel.html#L194) is trivial and whose real component [`LanglandsTunnell.ratArchGL2`](def/LanglandsTunnell_DeltaLift.html#L16) lies in $\mathrm{GL}_2^{+}(\mathbb{R})$, one has $\Phi(h) = (g \mid_{2} \mathrm{ratArchGL2}\, h)(i)$. Let $\mu_1, \mu_2 \colon \mathbb{Q}_q^{\times} \to \mathbb{C}^{\times}$ be group homomorphisms, and let $f$ be a $\mathbb{C}$-linear map from [`LocalNewvector.AdelicSpan`](def/LocalNewvector_AdelicSpanCarrier.html#L82) $\Phi$, the span of the $\mathrm{GL}_2$-adelic translates of $\Phi$ inside the carrier of complex-valued functions, to [`LocalNewvector.PSCarrier`](def/LocalNewvector_PrincipalSeriesCarrier.html#L173) $q\,\mu_1\,\mu_2$, the space of locally constant functions $F$ on $\mathrm{GL}_2(\mathbb{Q}_q)$ with $F(b(a_1,a_2,x)\,g) = \mu_1(a_1)\mu_2(a_2)\,\delta^{1/2}(a_1,a_2)\,F(g)$ for Borel elements [`LocalNewvector.borelElem`](def/LocalNewvector_PrincipalSeriesCarrier.html#L13). Assume $f$ commutes with the action of $\mathrm{GL}_2(\mathbb{Q}_q)$ and that $f \neq 0$. Then $\mu_1\mu_2$ is unramified in the sense of [`LocalNewvector.IsUnramified`](def/LocalNewvector_CharConductor.html#L11): $\mu_1(u)\mu_2(u) = 1$ for every $u \in \mathbb{Q}_q^{\times}$ with $\lVert u \rVert = 1$.
--
--   This records that the central character of a principal series $B(\mu_1,\mu_2)$ receiving a nonzero equivariant map from the span of translates of an adelic lift of a form on $\Gamma_0(M)$ must be unramified, the level-$M$ invariance of the lift forcing triviality of $\mu_1\mu_2$ on the units of $\mathbb{Z}_q$. It is used in the analysis of the local component at $q$ of such a lift, in particular in the statements describing newforms whose level is exactly divisible by $q^2$ and the characteristic polynomial of inertia at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsAdelicLiftOf_isUnramified_mul_of_linearMap_psCarrier_ne_zero.lean

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Definitions.Def_LocalNewvector_CharConductor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.IsAdelicLiftOf.isUnramified_mul_of_linearMap_psCarrier_ne_zero
    {M : ℕ} [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (q : ℕ) [Fact q.Prime]
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hgΦ : g.IsAdelicLiftOf Φ)
    (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ) (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂)
    (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v) (hne : f ≠ 0) :
    LocalNewvector.IsUnramified q (μ₁ * μ₂) := by sorry
