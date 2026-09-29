-- Prove2me | Theorems.Thm_CuspForm_IsEigenformWith_dvd_and_qCoeff_eq_or_not_dvd_and_qCoeff_sq_sub_eq_zero_of_isPrimitiveForm_of_not_sq_dvd
-- name    : CuspForm.IsEigenformWith.dvd_and_qCoeff_eq_or_not_dvd_and_qCoeff_sq_sub_eq_zero_of_isPrimitiveForm_of_not_sq_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/4e9a9c5f-8bf8-5d4a-b32e-e432e5458a50
-- title:
--   Uₚ-eigenvalue at a prime exactly dividing the level
-- statement:
--   Fix $N\ge 1$, an integer $k$, a Dirichlet character $\varepsilon$ modulo $N$ with values in $\mathbb{C}$, and a cusp form $h$ of weight $k$ on $\Gamma_1(N)$ satisfying [`CuspForm.IsEigenformWith`](def/CuspForm_PrimitiveFormGamma1.html#L19) $\varepsilon$: writing $a_n(\cdot)$ for the $n$-th coefficient [`ModularFormClass.qCoeff`](def/FLTPrelim_Modularity.html#L19) of the $q$-expansion of width $1$, one has $a_1(h)=1$; for every prime $p\nmid N$ and every $n$, $a_{pn}(h)+\varepsilon(p)p^{k-1}\,[p\mid n]\,a_{n/p}(h)=a_p(h)a_n(h)$; for every prime $\ell\mid N$ and every $n$, $a_{\ell n}(h)=a_\ell(h)a_n(h)$; and $h(\gamma\tau)=\varepsilon(\gamma_{11})(\gamma_{10}\tau+\gamma_{11})^k h(\tau)$ for all $\gamma\in\Gamma_0(N)$ and $\tau$ in the upper half-plane. Fix also $M\ge 1$, a Dirichlet character $\varepsilon_M$ modulo $M$, and a cusp form $g$ of weight $k$ on $\Gamma_1(M)$ which is a primitive form for $\varepsilon_M$, i.e. it satisfies the same eigenform conditions at level $M$ and moreover, for every divisor $M'\ne M$ of $M$, the eigenpacket $(n\mapsto a_n(g),\,n\mapsto\varepsilon_M(n))$ does not occur at level $M'$: there is no nonzero cusp form of weight $k$ on $\Gamma_1(M')$ with a nebentypus $\varepsilon'$ modulo $M'$ for which, outside some finite set of primes $p$, $\varepsilon'(p)=\varepsilon_M(p)$ and the above Hecke relation holds with eigenvalue $a_p(g)$. Assume $M\mid N$, that $\varepsilon_M$ induces $\varepsilon$ by change of level, and that $a_\ell(g)=a_\ell(h)$ for every prime $\ell\nmid N$. Then for every prime $p$ with $p\mid N$ and $p^2\nmid N$, either $p\mid M$ and $a_p(h)=a_p(g)$, or $p\nmid M$ and $a_p(h)^2-a_p(g)a_p(h)+\varepsilon_M(p)p^{k-1}=0$.
--
--   This is the classical description of the $U_p$-eigenvalue of a (not necessarily new) normalised eigenform at a prime exactly dividing the level, in terms of the primitive form carrying the same eigenpacket away from the level: in the $p$-new case the eigenvalue equals $a_p(g)$, and in the $p$-old case it is a root of the Hecke polynomial $X^2-a_p(g)X+\varepsilon_M(p)p^{k-1}$. It is used in the analysis of the local behaviour at $p$ of the Galois representation attached to $h$, in particular for the description of inertia at primes dividing the level to multiplicity one, and in the comparison of $U_p$-eigenvalues with coefficients of primitive forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsEigenformWith_dvd_and_qCoeff_eq_or_not_dvd_and_qCoeff_sq_sub_eq_zero_of_isPrimitiveForm_of_not_sq_dvd.lean

import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.IsEigenformWith.dvd_and_qCoeff_eq_or_not_dvd_and_qCoeff_sq_sub_eq_zero_of_isPrimitiveForm_of_not_sq_dvd
    {N : ℕ} [NeZero N] {k : ℤ} {ε : DirichletCharacter ℂ N}
    {h : CuspForm (CongruenceSubgroup.Gamma1 N) k} (hh : CuspForm.IsEigenformWith ε h)
    {M : ℕ} [NeZero M] {εM : DirichletCharacter ℂ M} {g : CuspForm (CongruenceSubgroup.Gamma1 M) k}
    (hg : CuspForm.IsPrimitiveForm εM g) (hMN : M ∣ N)
    (hε : DirichletCharacter.changeLevel hMN εM = ε)
    (hcoeff : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ModularFormClass.qCoeff g ℓ = ModularFormClass.qCoeff h ℓ)
    (p : ℕ) (hp : p.Prime) (hpN : p ∣ N) (hp2 : ¬ p ^ 2 ∣ N) :
    (p ∣ M ∧ ModularFormClass.qCoeff h p = ModularFormClass.qCoeff g p) ∨
    (¬ p ∣ M ∧
      ModularFormClass.qCoeff h p ^ 2 - ModularFormClass.qCoeff g p * ModularFormClass.qCoeff h p
        + εM (p : ZMod M) * (p : ℂ) ^ (k - 1) = 0) := by sorry
