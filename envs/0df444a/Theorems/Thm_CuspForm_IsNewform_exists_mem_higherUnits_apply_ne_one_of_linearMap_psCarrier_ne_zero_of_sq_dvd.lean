-- Prove2me | Theorems.Thm_CuspForm_IsNewform_exists_mem_higherUnits_apply_ne_one_of_linearMap_psCarrier_ne_zero_of_sq_dvd
-- name    : CuspForm.IsNewform.exists_mem_higherUnits_apply_ne_one_of_linearMap_psCarrier_ne_zero_of_sq_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/7e41f72b-1fc2-56d3-8848-08849010a8f1
-- title:
--   Ramified first character in a principal series at q² ∣ M
-- statement:
--   Let $M$ be a positive integer and let $g$ be a weight-two cusp form for $\Gamma_0(M)$ which is a newform in the sense of the project: $g$ is a normalised eigenform (its $q$-expansion coefficients satisfy $a_1(g)=1$, multiplicativity $a_{mn}=a_m a_n$ for coprime $m,n$, the recursion $a_{p^{r+2}}=a_p a_{p^{r+1}}-p\,a_{p^r}$ for primes $p\nmid M$ and $a_{p^{r+2}}=a_p a_{p^{r+1}}$ for $p \mid M$), and for no proper divisor $M'$ of $M$ does there exist a normalised eigenform of level $M'$ whose coefficients at the primes not dividing $M$ agree with those of $g$. Let $q$ be a prime with $q^2 \mid M$. Let $\Phi$ be a complex-valued function on $\mathrm{GL}_2$ of the adele ring of $\mathbb{Q}$ which is an adelic lift of $g$: it is invariant under left multiplication by the image of $\mathrm{GL}_2(\mathbb{Q})$, invariant under right multiplication by the finite adelic level-one subgroup for the ideal $(M)$, and at every adelic matrix $h$ whose finite component is trivial and whose real component lies in $\mathrm{GL}_2^{+}(\mathbb{R})$ one has $\Phi(h) = (g \mid_2 h_\infty)(i)$, where $h_\infty$ is the real matrix attached to $h$. Let $\mu_1,\mu_2 \colon \mathbb{Q}_q^{\times} \to \mathbb{C}^{\times}$ be group homomorphisms, and let $f$ be a $\mathbb{C}$-linear map from the adelic span of $\Phi$ (the span of the translates $g \cdot \Phi$, $g$ an adelic matrix) to the principal-series space attached to $\mu_1,\mu_2$, namely the space of locally constant functions $F$ on $\mathrm{GL}_2(\mathbb{Q}_q)$ with $F(b(a_1,a_2,x)\,h) = \mu_1(a_1)\mu_2(a_2)\,\delta^{1/2}(a_1,a_2)\,F(h)$ for Borel elements. Assume $f(x \cdot v) = x \cdot f(v)$ for all $x \in \mathrm{GL}_2(\mathbb{Q}_q)$ and all $v$ in the source, and $f \neq 0$. Then there is $u \in \mathbb{Q}_q^{\times}$ with $\|u\| = 1$ such that $\mu_1(u) \neq 1$; that is, $\mu_1$ is ramified. The conclusion is asserted for $\mu_1$ only, not for $\mu_2$.
--
--   This is the local statement that the component at $q$ of a newform whose level is divisible by $q^2$ cannot map nontrivially and equivariantly into a principal series with $\mu_1$ unramified, the input being that the new-vector conductor of the adelic span at $q$ equals the exponent of $q$ in $M$, here at least two. It is used in the determination of the characteristic polynomial of inertia at $q$ and in showing that the associated $\ell$-adic Galois representation is not unipotent on inertia at primes occurring to exponent two in the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNewform_exists_mem_higherUnits_apply_ne_one_of_linearMap_psCarrier_ne_zero_of_sq_dvd.lean

import Definitions.Def_CuspForm_AdelicLift
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.IsNewform.exists_mem_higherUnits_apply_ne_one_of_linearMap_psCarrier_ne_zero_of_sq_dvd
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (q : ℕ) [Fact q.Prime] (hqM : q ^ 2 ∣ M)
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)
    (hΦg : g.IsAdelicLiftOf Φ)
    (μ₁ μ₂ : ℚ_[q]ˣ →* ℂˣ)
    (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q μ₁ μ₂)
    (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v)
    (hne : f ≠ 0) :
    ∃ u ∈ LocalNewvector.higherUnits q 0, μ₁ u ≠ 1 := by sorry
