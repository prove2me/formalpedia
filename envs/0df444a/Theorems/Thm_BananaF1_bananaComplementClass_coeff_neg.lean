-- Prove2me | Theorems.Thm_BananaF1_bananaComplementClass_coeff_neg
-- name    : BananaF1.bananaComplementClass_coeff_neg
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T16:48:03.504614+00:00
-- url     : https://prove2.me/theorems/a433caae-58cc-404b-90e0-3259f13168d9
-- title:
--   Lemma 3.9 (second half): $[Y_{\Gamma_n}]$ has a negative coefficient
-- statement:
--   The second half of Lemma 3.9: the class of the hypersurface complement $Y_{\Gamma_n} = \mathbb{P}^{n-1} \smallsetminus X_{\Gamma_n}$,
--
--   $$[Y_{\Gamma_n}] \;=\; \mathbb{T}^{n-1} + (n-1)\mathbb{T}^{n-2} + \mathbb{T}^{n-3} - \mathbb{T}^{n-4} + \cdots \pm 1,$$
--
--   fails the non-negativity condition of Lemma 3.8. The statement exhibits one explicit negative coefficient: for every $n \ge 4$ the coefficient of $\mathbb{T}^{n-4}$ equals $-1$. Consequently $[Y_{\Gamma_n}]$ is not of the form $\sum_k a_k \mathbb{T}^k$ with all $a_k \ge 0$, so the complement admits no torification in the sense of the source, in contrast with $X_{\Gamma_n}$.
-- source:
--   D. Bejleri, M. Marcolli, Quantum field theory over F_1, Journal of Geometry and Physics (2013), doi:10.1016/j.geomphys.2013.03.002 (https://doi.org/10.1016/j.geomphys.2013.03.002); Section 3.6, Lemma 3.9 together with equations (3.8), (3.9), (3.10), and the necessary conditions of Section 3.3 Proposition 3.1 and Section 3.5 Lemma 3.8. The closed formula (3.8) is Theorem 3.10 of P. Aluffi, M. Marcolli, Feynman motives of banana graphs, Commun. Number Theory Phys. 3 (2009), no. 1, 1-57, and the complement formula is Corollary 3.13 there.

import Definitions.Def_bananaF1Classes
open Polynomial

namespace BananaF1

theorem bananaComplementClass_coeff_neg (n : ℕ) (hn : 4 ≤ n) :
    (bananaComplementClass n).coeff (n - 4) = -1 := by sorry

end BananaF1
