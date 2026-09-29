-- Prove2me | Theorems.Thm_CuspForm_IsPrimitiveForm_factorization_le_of_mem_span_of_mem_fixedSubmodule_padicK1
-- name    : CuspForm.IsPrimitiveForm.factorization_le_of_mem_span_of_mem_fixedSubmodule_padicK1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/88581713-da48-5d1f-b052-5457ca771d74
-- title:
--   Casselman lower bound: K₁(q^m)-fixed vector forces v_q(M)≤ m
-- statement:
--   Let $M$ be a positive integer, $\varepsilon$ a Dirichlet character modulo $M$ with values in $\mathbb C$, and $h$ a cusp form of weight $2$ on $\Gamma_1(M)$ that is primitive for $\varepsilon$ in the sense of [`CuspForm.IsPrimitiveForm`](def/CuspForm_PrimitiveFormGamma1.html#L38): its first $q$-expansion coefficient is $1$, it satisfies the Hecke relations $a_{pn}+\varepsilon(p)p^{k-1}a_{n/p}=a_pa_n$ at primes $p\nmid M$ and the multiplicativity $a_{\ell n}=a_\ell a_n$ at primes $\ell\mid M$, it has nebentypus $\varepsilon$, and for no proper divisor $M'$ of $M$ does the packet consisting of its coefficients and the values of $\varepsilon$ occur at level $M'$ (no nonzero weight-two cusp form on $\Gamma_1(M')$ with some nebentypus reproduces them outside a finite set of primes). Let $q$ be a prime and let $\Phi$ be a complex-valued function on $\mathrm{GL}_2$ of the adele ring of $\mathbb Q$ which is an adelic lift of $h$: left invariant under the global points $\mathrm{GL}_2(\mathbb Q)$, right invariant under the finite level-one subgroup attached to the ideal $(M)$ of $\mathcal O_{\mathbb Q}$, and equal, at adelic matrices with trivial finite part and totally positive archimedean part, to $(h\mid_2 g_\infty)(i)$. Let $m\ge 1$, and let $y$ be an element of the span of the $\mathrm{GL}_2(\mathbb A)$-translates of $\Phi$ which lies in the $\mathbb C$-span of the translates $x\cdot\Phi$ with $x\in\mathrm{GL}_2(\mathbb Q_q)$, is fixed by every element of the subgroup [`LocalNewvector.padicK1 q m`](def/LocalNewvector_CongruenceSubgroupK1.html#L161) of $\mathrm{GL}_2(\mathbb Q_q)$ (the `congruenceK1` subgroup attached to $q\in\mathbb Z_q$ and the integer $m$), and is nonzero. Then the exponent of $q$ in the factorization of $M$ is at most $m$.
--
--   This is the lower-bound half of Casselman's comparison between the exponent of a prime in the level of a newform and the conductor exponent of the corresponding local component at that prime, the upper bound being the right $K_1(M)$-invariance of the adelic lift itself. It is used in [`CuspForm.IsPrimitiveForm.factorization_eq_conductor_factorization_or_of_linearMap_psCarrier_isUnramified`](thm.html#CuspForm.IsPrimitiveForm.factorization_eq_conductor_factorization_or_of_linearMap_psCarrier_isUnramified), where the level of a primitive form is matched against local conductor data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsPrimitiveForm_factorization_le_of_mem_span_of_mem_fixedSubmodule_padicK1.lean

import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_LocalNewvector_AdelicSpanCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.IsPrimitiveForm.factorization_le_of_mem_span_of_mem_fixedSubmodule_padicK1
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hh : CuspForm.IsPrimitiveForm ε h)
    (q : ℕ) [Fact q.Prime]
    (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)
    (hΦh : CuspForm.IsAdelicLiftOfGamma1 h Φ)
    {m : ℕ} (hm : 1 ≤ m)
    (y : LocalNewvector.AdelicSpan Φ)
    (hy : y ∈ Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self Φ))
    (hfix : y ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q m) (LocalNewvector.AdelicSpan Φ))
    (hy0 : y ≠ 0) :
    M.factorization q ≤ m := by sorry
