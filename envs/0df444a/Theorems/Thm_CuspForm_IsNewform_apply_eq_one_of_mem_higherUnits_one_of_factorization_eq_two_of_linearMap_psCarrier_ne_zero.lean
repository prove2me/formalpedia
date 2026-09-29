-- Prove2me | Theorems.Thm_CuspForm_IsNewform_apply_eq_one_of_mem_higherUnits_one_of_factorization_eq_two_of_linearMap_psCarrier_ne_zero
-- name    : CuspForm.IsNewform.apply_eq_one_of_mem_higherUnits_one_of_factorization_eq_two_of_linearMap_psCarrier_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/53f7fc66-1569-5a99-8c91-4cd970a6b1a6
-- title:
--   Principal-series characters trivial on 1+qℤ_q when v_q(M)=2
-- statement:
--   Let $M\ge 1$ and let $g$ be a weight-two cusp form on $\Gamma_0(M)$ which is a newform in the project's sense: $g$ is a normalised eigenform (its $q$-coefficient at $1$ is $1$, its coefficients are multiplicative at coprime indices, and they satisfy the two prime-power recursions according as the prime divides $M$ or not), and for no proper divisor $M'$ of $M$ does there exist a normalised eigenform of weight two on $\Gamma_0(M')$ whose $q$-coefficients at the primes not dividing $M$ agree with those of $g$. Let $q$ be a prime with $M.\mathrm{factorization}\,q = 2$, i.e. $v_q(M)=2$. Let $\Phi\colon \mathrm{GL}_2(\mathbb{A}_\mathbb{Q})\to\mathbb{C}$ be non-zero and an adelic lift of $g$, meaning: $\Phi$ is left invariant under the image of $\mathrm{GL}_2(\mathbb{Q})$, right invariant under the finite level-one subgroup attached to the ideal $(M)$ of $\mathcal{O}_\mathbb{Q}$ embedded into adelic $\mathrm{GL}_2$, and for $h$ with trivial finite component and archimedean component in $\mathrm{GL}_2^+(\mathbb{R})$ one has $\Phi(h) = (g\mid_2 \mathrm{ratArchGL2}\,h)(i)$. Let $\mu_1,\mu_2\colon \mathbb{Q}_q^\times\to\mathbb{C}^\times$ be group homomorphisms and let $f$ be a non-zero $\mathbb{C}$-linear map from [`LocalNewvector.AdelicSpan`](def/LocalNewvector_AdelicSpanCarrier.html#L82) $\Phi$ (the span of the $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$-translates of $\Phi$) to the principal series `PSCarrier` $q\,\mu_1\,\mu_2$ (locally constant $F\colon \mathrm{GL}_2(\mathbb{Q}_q)\to\mathbb{C}$ with $F(b(a_1,a_2,x)g) = \mu_1(a_1)\mu_2(a_2)\,\delta^{1/2}(a_1,a_2)F(g)$), commuting with the action of $\mathrm{GL}_2(\mathbb{Q}_q)$. Then for every $u\in\mathbb{Q}_q^\times$ with $\|u\|=1$ and $\|u-1\|\le q^{-1}$ one has $\mu_1(u)=1$ and $\mu_2(u)=1$.
--
--   This is the case $v_q(M)=2$ of the comparison between the level of a weight-two newform and the conductor exponents of the characters of a principal-series local component at $q$: both characters are trivial on the principal units $1+q\mathbb{Z}_q$, so each has conductor exponent at most one. It feeds the construction, at a prime dividing the level exactly twice, of a primitive form whose local principal series is unramified, used in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNewform_apply_eq_one_of_mem_higherUnits_one_of_factorization_eq_two_of_linearMap_psCarrier_ne_zero.lean

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.IsNewform.apply_eq_one_of_mem_higherUnits_one_of_factorization_eq_two_of_linearMap_psCarrier_ne_zero
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (q : ℕ) [Fact q.Prime] (hM2 : M.factorization q = 2)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hΦ0 : Φ ≠ 0)
    (hΦg : g.IsAdelicLiftOf Φ)
    (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ)
    (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂)
    (hfequiv : ∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v)
    (hf0 : f ≠ 0) :
    ∀ u ∈ LocalNewvector.higherUnits q 1, μ₁ u = 1 ∧ μ₂ u = 1 := by sorry
