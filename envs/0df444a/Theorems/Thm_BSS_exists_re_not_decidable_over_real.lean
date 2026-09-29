-- Prove2me | Theorems.Thm_BSS_exists_re_not_decidable_over_real
-- name    : BSS.exists_re_not_decidable_over_real
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T15:43:22.375368+00:00
-- url     : https://prove2.me/theorems/dd7f2224-06fc-4b9e-a805-862b770c5e8b
-- title:
--   §8: there is a set R.E. over $\mathbb{R}$ that is not decidable over $\mathbb{R}$
-- statement:
--   The corollary drawn at the end of §8 (p. 36): the existence of the universal machine $U$ over $R$
--   may be used to construct R.E. subsets of $R^\infty$ that are not decidable, by the usual Cantor
--   diagonal argument; in particular the halting set $\Omega_U$ of the universal machine is such a
--   set.
--
--   The statement asks only for the existence of some set that is R.E. over $\mathbb{R}$ but not
--   decidable over $\mathbb{R}$, which is the form in which the conclusion is used; constructing the
--   universal machine of §8 is the expected route to it.
-- source:
--   L. Blum, M. Shub, S. Smale, On a theory of computation and complexity over the real numbers: NP-completeness, recursive functions and universal machines, Bull. Amer. Math. Soc. (N.S.) 21 (1989), no. 1, 1-46, https://doi.org/10.1090/S0273-0979-1989-15750-9, §8, p. 36, closing remark; universal machine, §8, pp. 33-36

import Definitions.Def_BSSFeasibility

namespace BSS

theorem exists_re_not_decidable_over_real :
    ∃ S : Set (Rinf ℝ), IsREOver ℝ S ∧ ¬ IsDecidableOver ℝ S := by sorry

end BSS
