-- Prove2me | Theorems.Thm_CuspForm_IsNewform_exists_gamma1_coe_eq_and_isPrimitiveForm_one
-- name    : CuspForm.IsNewform.exists_gamma1_coe_eq_and_isPrimitiveForm_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/deb32e1e-c8ca-5cd3-9244-f749e669beb0
-- title:
--   Weight-two Γ₀(N) newforms are primitive with trivial nebentypus
-- statement:
--   Let $N$ be a positive integer and let $g$ be a weight-two cusp form for $\Gamma_0(N)$ which is a newform in the $\Gamma_0$ sense, i.e. (i) $g$ is a normalised eigenform: its $q$-expansion coefficients satisfy $a_1(g)=1$, $a_{mn}(g)=a_m(g)a_n(g)$ for coprime $m,n$, $a_{p^{r+2}}(g)=a_p(g)a_{p^{r+1}}(g)-p\,a_{p^r}(g)$ for primes $p\nmid N$, and $a_{p^{r+2}}(g)=a_p(g)a_{p^{r+1}}(g)$ for primes $p\mid N$; and (ii) for every divisor $M$ of $N$ with $M\neq N$ there is no normalised eigenform of weight two on $\Gamma_0(M)$ whose coefficients $a_\ell$ agree with those of $g$ at all primes $\ell\nmid N$. Then there exists a weight-two cusp form $g_1$ for $\Gamma_1(N)$ which, as a function on the upper half-plane, is equal to $g$, and which is a primitive form for the trivial Dirichlet character $\mathbf 1$ modulo $N$: $a_1(g_1)=1$; for every prime $p\nmid N$ and every $n$, $a_{pn}(g_1)+\mathbf 1(p)\,p\,[\,p\mid n\,]\,a_{n/p}(g_1)=a_p(g_1)a_n(g_1)$; for every prime $\ell\mid N$ and every $n$, $a_{\ell n}(g_1)=a_\ell(g_1)a_n(g_1)$; the predicate [`CuspForm.HasNebentypus`](def/CuspForm_PrimitiveFormGamma1.html#L13) holds for $g_1$ with character $\mathbf 1$; and for every divisor $M'$ of $N$ with $M'\neq N$ the eigenpacket of $g_1$ does not occur in weight two at level $M'$, i.e. there are no Dirichlet character $\varepsilon'$ modulo $M'$ and nonzero $h\in S_2(\Gamma_1(M'))$ with nebentypus $\varepsilon'$ admitting a finite set $S$ of primes outside which $\varepsilon'(p)=\mathbf 1(p)$ and $a_{pn}(h)+\varepsilon'(p)\,p\,[\,p\mid n\,]\,a_{n/p}(h)=a_p(g_1)a_n(h)$ for all $n$.
--
--   This is the dictionary between the two standard notions of newform in weight two: the formulation by normalised Hecke eigenforms on $\Gamma_0(N)$ minimal among levels dividing $N$, and the Atkin–Lehner notion of a primitive form on $\Gamma_1(N)$ with nebentypus, here at the trivial character. It feeds the analysis of Hecke eigenspaces and of the span of oldforms used downstream, being cited by [`CuspForm.IsNewform.maxGenEigenspace_heckeTLinH_le_and_exists_oldClasses_span_eq_iInf_eigenspace`](thm.html#CuspForm.IsNewform.maxGenEigenspace_heckeTLinH_le_and_exists_oldClasses_span_eq_iInf_eigenspace).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNewform_exists_gamma1_coe_eq_and_isPrimitiveForm_one.lean

import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.IsNewform.exists_gamma1_coe_eq_and_isPrimitiveForm_one
    {N : ℕ} [NeZero N] {g : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hg : g.IsNewform) :
    ∃ g₁ : CuspForm (CongruenceSubgroup.Gamma1 N) 2,
      (g₁ : UpperHalfPlane → ℂ) = (g : UpperHalfPlane → ℂ) ∧
        CuspForm.IsPrimitiveForm (1 : DirichletCharacter ℂ N) g₁ := by sorry
