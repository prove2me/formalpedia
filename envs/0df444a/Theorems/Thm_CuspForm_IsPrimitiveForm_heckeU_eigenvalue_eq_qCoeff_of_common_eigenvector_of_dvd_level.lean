-- Prove2me | Theorems.Thm_CuspForm_IsPrimitiveForm_heckeU_eigenvalue_eq_qCoeff_of_common_eigenvector_of_dvd_level
-- name    : CuspForm.IsPrimitiveForm.heckeU_eigenvalue_eq_qCoeff_of_common_eigenvector_of_dvd_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/3ffde793-be5e-585f-a419-b6a3edcb4c3f
-- title:
--   U_q acts by a_q(G) on the old packet, q² ∤ N
-- statement:
--   Let $M \mid N$ be nonzero naturals, let $\chi$ be a Dirichlet character mod $M$ with values in $\mathbb{C}$, and let $G$ be a weight $2$ cusp form on $\Gamma_1(M)$ which is primitive of nebentypus $\chi$ in the sense of [`CuspForm.IsPrimitiveForm`](def/CuspForm_PrimitiveFormGamma1.html#L38): writing $a_n(\cdot)$ for the $n$-th coefficient of the $q$-expansion of width $1$, one has $a_1(G)=1$, the relation $a_{pn}(G)+\chi(p)p^{k-1}[p\mid n]a_{n/p}(G)=a_p(G)a_n(G)$ for all primes $p\nmid M$ and all $n$, the relation $a_{\ell n}(G)=a_\ell(G)a_n(G)$ for primes $\ell\mid M$, $G$ has nebentypus $\chi$, and the eigenpacket $(a_n(G),\chi)$ does not occur at any proper divisor level $M'\mid M$, $M'\neq M$. Let $S$ be a finite set of naturals, let $v\neq0$ be a weight $2$ cusp form on $\Gamma_1(N)$, and let $t,u,\delta:\mathbb{N}\to\mathbb{C}$ satisfy: `heckeTLinOne` at each prime $\ell\nmid N$ sends $v$ to $t(\ell)\cdot v$; the diamond operator `diamondLinOne` at each $d$ coprime to $N$ sends $v$ to $\delta(d)\cdot v$; $a_{\ell n}(v)=u(\ell)a_n(v)$ for all $n$ and all primes $\ell\mid N$; and $t(\ell)=a_\ell(G)$, $\delta(\ell)=\chi(\ell \bmod M)$ for all primes $\ell\nmid N$ outside $S$. Then for every prime $q$ with $q\mid M$ and $q^2\nmid N$ one has $u(q)=a_q(G)$.
--
--   This is the old-space half of strong multiplicity one in the form due to Atkin–Lehner and Li: a common Hecke–diamond eigenvector at level $N$ whose good eigenpacket agrees almost everywhere with that of a primitive form $G$ of level $M\mid M$ dividing $N$ has $U_q$-eigenvalue exactly $a_q(G)$ at those primes $q\mid M$ with $q^2\nmid N$. It feeds the description of the action of the rational Hecke algebra at level $N$ on the $G$-old packet used later in the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsPrimitiveForm_heckeU_eigenvalue_eq_qCoeff_of_common_eigenvector_of_dvd_level.lean

import Mathlib
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_CuspForm_Gamma1HeckeOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.IsPrimitiveForm.heckeU_eigenvalue_eq_qCoeff_of_common_eigenvector_of_dvd_level
    {M : ℕ} [NeZero M] {N : ℕ} [NeZero N] (hMN : M ∣ N)
    {χ : DirichletCharacter ℂ M} {G : CuspForm (CongruenceSubgroup.Gamma1 M) 2}
    (hG : CuspForm.IsPrimitiveForm χ G)
    (S : Finset ℕ) (v : CuspForm (CongruenceSubgroup.Gamma1 N) 2) (hv0 : v ≠ 0)
    (t u δ : ℕ → ℂ)
    (hvT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), CuspForm.heckeTLinOne 2 hℓ hℓN v = t ℓ • v)
    (hvD : ∀ d : ℕ, Nat.Coprime d N → CuspForm.diamondLinOne N 2 d v = δ d • v)
    (hvU : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ N → ∀ n : ℕ,
      ModularFormClass.qCoeff v (ℓ * n) = u ℓ * ModularFormClass.qCoeff v n)
    (ht : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S → t ℓ = ModularFormClass.qCoeff G ℓ)
    (hδ : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S → δ ℓ = χ (ℓ : ZMod M))
    {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (hq2 : ¬ q ^ 2 ∣ N) :
    u q = ModularFormClass.qCoeff G q := by sorry
