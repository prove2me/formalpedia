-- Prove2me | Theorems.Thm_CuspForm_IsPrimitiveForm_factorization_eq_conductor_factorization_or_of_linearMap_psCarrier_isUnramified
-- name    : CuspForm.IsPrimitiveForm.factorization_eq_conductor_factorization_or_of_linearMap_psCarrier_isUnramified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/61eeeaf0-2f88-5768-a126-45434d3dfb92
-- title:
--   Principal series with unramified character: v_q(M) versus v_q(cond ε)
-- statement:
--   Let $M$ be a positive integer, let $\varepsilon$ be a Dirichlet character modulo $M$ with values in $\mathbb{C}$, and let $h$ be a cusp form of weight $2$ on $\Gamma_1(M)$ which is primitive with nebentypus $\varepsilon$, that is: its first $q$-expansion coefficient is $1$, it satisfies the Hecke relations $a_{pn}+\varepsilon(p)p^{k-1}a_{n/p}=a_pa_n$ for primes $p\nmid M$ and the multiplicativity $a_{\ell n}=a_\ell a_n$ for primes $\ell\mid M$, it has nebentypus $\varepsilon$, and for no proper divisor $M'$ of $M$ does the eigenpacket formed by the coefficients of $h$ and the values of $\varepsilon$ occur in weight $k$ at level $M'$. Let $q$ be a prime and let $\Phi$ be a complex-valued function on $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$ which is an adelic lift of $h$: it is invariant under left translation by the image of $\mathrm{GL}_2(\mathbb{Q})$, invariant under right translation by the finite level-one subgroup attached to the ideal $(M)$, and at every adelic matrix whose finite part is $1$ and whose real component lies in $\mathrm{GL}_2^{+}(\mathbb{R})$ its value is $(h\mid_2 g_\infty)(i)$, $g_\infty$ being that real component. Let $\nu_1,\nu_2\colon\mathbb{Q}_q^\times\to\mathbb{C}^\times$ be characters, and let $f$ be a $\mathbb{C}$-linear map from the span of the $\mathrm{GL}_2$-adelic translates of $\Phi$ to the principal series space of locally constant functions $F$ on $\mathrm{GL}_2(\mathbb{Q}_q)$ satisfying $F(b(a_1,a_2,x)g)=\nu_1(a_1)\nu_2(a_2)\,\delta^{1/2}(a_1,a_2)F(g)$ for Borel elements, such that $f(x\cdot v)=x\cdot f(v)$ for all $x\in\mathrm{GL}_2(\mathbb{Q}_q)$, with $f\neq 0$, and assume $\nu_1$ is unramified, i.e. $\nu_1(u)=1$ whenever $\|u\|=1$. Then either the exponent of $q$ in $M$ equals the exponent of $q$ in the conductor of $\varepsilon$, or else $q\mid M$, $q^2\nmid M$ and $q\nmid\mathrm{cond}\,\varepsilon$.
--
--   This is the purely automorphic comparison of the $q$-exponent of the level with that of the nebentypus conductor for a primitive form whose local component at $q$ admits a nonzero equivariant map into a principal series with one unramified inducing character; no Galois-theoretic assertion is involved. It feeds the two statements that, at a prime with $v_q(M)=2$, produce a primitive form with such a principal-series map, and that, at a prime with $v_q(M)=1$, produce an adic Galois representation fixed by the inertia subgroup at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsPrimitiveForm_factorization_eq_conductor_factorization_or_of_linearMap_psCarrier_isUnramified.lean

import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.IsPrimitiveForm.factorization_eq_conductor_factorization_or_of_linearMap_psCarrier_isUnramified
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hh : CuspForm.IsPrimitiveForm ε h)
    (q : ℕ) [Fact q.Prime]
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)
    (hΦh : CuspForm.IsAdelicLiftOfGamma1 h Φ)
    (ν₁ ν₂ : ℚ_[q]ˣ →* ℂˣ) (f : LocalNewvector.AdelicSpan Φ →ₗ[ℂ] LocalNewvector.PSCarrier q ν₁ ν₂)
    (hfequiv : ∀ (x : GL (Fin 2) ℚ_[q]) (v : LocalNewvector.AdelicSpan Φ), f (x • v) = x • f v)
    (hf0 : f ≠ 0)
    (hν₁ : LocalNewvector.IsUnramified q ν₁) :
    M.factorization q = ε.conductor.factorization q ∨
      (q ∣ M ∧ ¬ q ^ 2 ∣ M ∧ ¬ q ∣ ε.conductor) := by sorry
