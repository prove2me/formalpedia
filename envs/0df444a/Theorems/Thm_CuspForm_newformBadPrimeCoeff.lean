-- Prove2me | Theorems.Thm_CuspForm_newformBadPrimeCoeff
-- name    : CuspForm.newformBadPrimeCoeff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/9f2a6d13-5c46-520c-b8dd-c27ab95cfc5d
-- title:
--   Bad-prime coefficients of weight-2 newforms on Γ₀(N)
-- statement:
--   For an arbitrary natural number $N$ the statement asserts the project's predicate [`CuspForm.NewformBadPrimeCoeff N`](def/CuspForm_Newforms.html#L42), which unfolds to the following. Let $f$ be a cusp form of weight $2$ for $\Gamma_0(N)$ which is a newform in the project's sense, namely: (i) $f$ is a normalised eigenform, meaning that its $q$-expansion coefficients $a_n =$ `qCoeff f n` (the coefficients of the width-$1$ $q$-expansion of $f$) satisfy $a_1 = 1$, $a_{mn} = a_m a_n$ for coprime $m, n$, the recursion $a_{p^{r+2}} = a_p a_{p^{r+1}} - p\,a_{p^{r}}$ for primes $p \nmid N$, and the recursion $a_{p^{r+2}} = a_p a_{p^{r+1}}$ for primes $p \mid N$; and (ii) $f$ is not old, in the sense that for no proper divisor $M \mid N$, $M \neq N$, does there exist a normalised eigenform $g$ of weight $2$ for $\Gamma_0(M)$ with $a_\ell(g) = a_\ell(f)$ for every prime $\ell \nmid N$. Then for every prime $q$ dividing $N$ both of the following hold: if $q^2 \nmid N$ then $a_q(f)^2 = 1$, and if $q^2 \mid N$ then $a_q(f) = 0$. No positivity hypothesis is imposed on $N$ and no hypothesis beyond newness is imposed on $f$; newness is thus formulated purely at the level of eigensystems of coefficients away from $N$, rather than through degeneracy maps or the old subspace.
--
--   These are the Atkin–Lehner–Li relations for the Hecke eigenvalue of a weight-$2$ newform at a prime dividing its level: $a_q^2 = 1$ when $q$ exactly divides $N$ (so that $a_q$ is, up to sign, the Atkin–Lehner eigenvalue of $W_q$) and $a_q = 0$ when $q^2 \mid N$. The formal statement differs from the textbook one in that newness is encoded as the non-existence of a normalised eigenform of strictly smaller level sharing all coefficients at primes prime to $N$, and in that both clauses are packaged into a single proposition valid for every level. Within the project the first clause supplies the $U_q$-eigenvalue criterion [`CuspForm.IsNewAt`](def/FreyPackage_LevelRaising.html#L14) used in the level-lowering steps, in particular the Mazur–Ribet lowering at $p$ ([`FreyPackage.level_lowering_at_p_of_conductorLevel`](thm.html#FreyPackage.level_lowering_at_p_of_conductorLevel)), while both clauses feed the newform lemmas on rescalings of forms between levels and on slash-operator identities for the $q$-th coefficient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_newformBadPrimeCoeff.lean

import Definitions.Def_CuspForm_Newforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.newformBadPrimeCoeff (N : ℕ) :
    CuspForm.NewformBadPrimeCoeff N := by sorry
