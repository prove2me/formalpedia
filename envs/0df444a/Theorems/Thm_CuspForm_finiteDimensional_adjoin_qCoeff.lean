-- Prove2me | Theorems.Thm_CuspForm_finiteDimensional_adjoin_qCoeff
-- name    : CuspForm.finiteDimensional_adjoin_qCoeff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/2ff31a43-170f-5d95-a633-bbaa5bcec813
-- title:
--   The Hecke field of a weight-2 eigenform is a number field
-- statement:
--   Let $N$ be a nonzero natural number and let $g$ be a cusp form of weight $2$ for the congruence subgroup $\Gamma_0(N)$. Write $a_n(g)$ for the $n$-th coefficient of the $q$-expansion of $g$ of width $1$, as computed by [`ModularFormClass.qCoeff`](def/FLTPrelim_Modularity.html#L19). Assume $g$ satisfies the predicate [`CuspForm.IsNormalizedEigenform`](def/FLTPrelim_Modularity.html#L28), i.e. the four conditions: $a_1(g)=1$; $a_{mn}(g)=a_m(g)\,a_n(g)$ for all coprime $m,n$; for every prime $p$ not dividing $N$ and every $r\ge 0$, $a_{p^{r+2}}(g)=a_p(g)\,a_{p^{r+1}}(g)-p\,a_{p^{r}}(g)$; and for every prime $p$ dividing $N$ and every $r\ge 0$, $a_{p^{r+2}}(g)=a_p(g)\,a_{p^{r+1}}(g)$. The conclusion is that the intermediate field of $\mathbb{C}/\mathbb{Q}$ generated over $\mathbb{Q}$ by the set $\{a_n(g) : n\in\mathbb{N}\}$ of all $q$-expansion coefficients is finite-dimensional as a $\mathbb{Q}$-vector space; that is, the coefficient field $\mathbb{Q}(a_n(g) : n \in \mathbb{N})$ is a number field. No holomorphy, Hecke-operator or newform hypothesis beyond the listed coefficient identities is imposed.
--
--   This is the finiteness of the Hecke field (coefficient field) of a weight-2 normalised eigenform on $\Gamma_0(N)$. It underlies the passage from an eigenform to the number field over which its associated Galois representations are defined, and is used in the construction of the $\ell$-adic representation attached to an eigenform with prescribed Frobenius characteristic polynomials, in the comparison of Hecke eigensystems on cohomology, and in the level-structure bookkeeping for newforms attached to elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_finiteDimensional_adjoin_qCoeff.lean

import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.finiteDimensional_adjoin_qCoeff {N : ℕ} [NeZero N]
    {g : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hg : g.IsNormalizedEigenform) :
    FiniteDimensional ℚ
      (IntermediateField.adjoin ℚ (Set.range fun n : ℕ => ModularFormClass.qCoeff g n)) := by sorry
