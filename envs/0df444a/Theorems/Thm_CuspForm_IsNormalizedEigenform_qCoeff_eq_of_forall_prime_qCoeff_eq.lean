-- Prove2me | Theorems.Thm_CuspForm_IsNormalizedEigenform_qCoeff_eq_of_forall_prime_qCoeff_eq
-- name    : CuspForm.IsNormalizedEigenform.qCoeff_eq_of_forall_prime_qCoeff_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/49a7ec34-b9a3-559a-b651-fdb161706c8e
-- title:
--   Agreement at primes forces agreement of all q-coefficients
-- statement:
--   Let $N$ be a natural number and let $f,g$ be cusp forms of weight $2$ for $\Gamma_0(N)$, where for a function on the upper half-plane $\mathrm{qCoeff}\,f\,n$ denotes the $n$-th coefficient of its $q$-expansion of width $1$. Assume that $f$ and $g$ both satisfy the predicate `IsNormalizedEigenform`, i.e. each $h \in \{f,g\}$ has $\mathrm{qCoeff}\,h\,1 = 1$, satisfies $\mathrm{qCoeff}\,h\,(mn) = \mathrm{qCoeff}\,h\,m \cdot \mathrm{qCoeff}\,h\,n$ for all coprime $m,n$, satisfies the recursion $\mathrm{qCoeff}\,h\,(p^{r+2}) = \mathrm{qCoeff}\,h\,p \cdot \mathrm{qCoeff}\,h\,(p^{r+1}) - p\,\mathrm{qCoeff}\,h\,(p^{r})$ for every prime $p \nmid N$ and every $r$, and satisfies $\mathrm{qCoeff}\,h\,(p^{r+2}) = \mathrm{qCoeff}\,h\,p \cdot \mathrm{qCoeff}\,h\,(p^{r+1})$ for every prime $p \mid N$ and every $r$. Assume further that $\mathrm{qCoeff}\,f\,p = \mathrm{qCoeff}\,g\,p$ for every prime $p$. Then for every natural number $n$ one has $\mathrm{qCoeff}\,f\,n = \mathrm{qCoeff}\,g\,n$; note that the conclusion is asserted for arbitrary $n$, including $n = 0$.
--
--   This is the standard statement that the Hecke recursions reconstruct all Fourier coefficients of a normalised eigenform from its prime-indexed coefficients, so that the eigensystem $(a_p)_p$ determines the whole $q$-expansion. It is the coefficient-level input to [`CuspForm.IsNormalizedEigenform.eq_of_forall_prime_qCoeff_eq`](thm.html#CuspForm.IsNormalizedEigenform.eq_of_forall_prime_qCoeff_eq), the weak multiplicity-one statement used in the newform layer of the level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNormalizedEigenform_qCoeff_eq_of_forall_prime_qCoeff_eq.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularFormClass

theorem CuspForm.IsNormalizedEigenform.qCoeff_eq_of_forall_prime_qCoeff_eq {N : ℕ}
    {f g : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform)
    (hg : g.IsNormalizedEigenform)
    (h : ∀ p : ℕ, p.Prime → qCoeff f p = qCoeff g p) (n : ℕ) :
    qCoeff f n = qCoeff g n := by sorry
