-- Prove2me | Theorems.Thm_BordenaveCollins_exists_expFix_eq_rational
-- name    : BordenaveCollins.exists_expFix_eq_rational
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-16T02:09:45.549204+00:00
-- url     : https://prove2.me/theorems/cc670e93-37a1-4ac7-8581-86181b762c4f
-- title:
--   The expected number of fixed points of a word in random permutations and perfect matchings is a rational function of 1/N
-- statement:
--   Fix $r$, $s$ and $q \ge 1$. There is a real polynomial $g_q$ of degree at most $(r+s)q$, with $\tfrac12 \le g_q(x) \le 1$ for $0 \le x \le \frac{1}{4(r+s+1)q^2}$, such that for every $g \in F_r * \Gamma_s$ of word length at most $q$ there is a real polynomial $f$ of degree at most $(r+s+2)q$ with
--   $$\mathbf E\big[\#\mathrm{fix}\, g(\sigma_1, \dots, \sigma_r, M_1, \dots, M_s)\big] = N \cdot \frac{f(1/N)}{g_q(1/N)}$$
--   for every admissible $N \ge q$ (any $N$ if $s = 0$, even $N$ otherwise). Here $\sigma_1, \dots, \sigma_r$ are independent uniform permutations and $M_1, \dots, M_s$ independent uniform perfect matchings of $N$ points, and $g(\sigma, M)$ is the image of $g$ under the homomorphism sending $u_i$ to $\sigma_i$ and $m_j$ to $M_j$.
--
--   This is Lemma 5.1 of Chen, Garza-Vargas, Tropp and van Handel, *A new approach to strong convergence*, with perfect matchings added to the model; the polynomial $g_q$ does not depend on $g$.
--
--   **Formalization note.** The definitions (`expFix`, `Adm`, `len`) are in the bundle `Def_BordenaveCollins`. The expectation is the average over the finite sample space. The degree bounds are cruder than those of the paper's Lemma 5.1. The bounds $\tfrac12 \le g_q \le 1$ are stated on $[0, \frac{1}{4(r+s+1)q^2}]$ only, which contains $1/N$ for $N \ge 4(r+s+1)q^2$, while the identity is stated for all admissible $N \ge q$.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 19-20, Lemma 5.1, adapted to permutations and perfect matchings; a step of our proof of the theorem of Bordenave, C. and Collins, B., Eigenvalues of random lifts and polynomials of random permutation matrices, Ann. of Math. (2) 190 (2019) 811–875, https://doi.org/10.4007/annals.2019.190.3.3

import Mathlib
import Definitions.Def_BordenaveCollins

open Polynomial

namespace BordenaveCollins

theorem exists_expFix_eq_rational (r s q : ℕ) (hq : 1 ≤ q) :
    ∃ gq : ℝ[X], gq.natDegree ≤ (r + s) * q ∧
      (∀ x ∈ Set.Icc (0 : ℝ) (1 / (4 * ((r : ℝ) + s + 1) * (q : ℝ) ^ 2)),
        1 / 2 ≤ gq.eval x ∧ gq.eval x ≤ 1) ∧
      ∀ g : G r s, len g ≤ q → ∃ f : ℝ[X], f.natDegree ≤ (r + s + 2) * q ∧
        ∀ N : ℕ, Adm s N → q ≤ N →
          expFix r s N g = N * (f.eval (1 / (N : ℝ)) / gq.eval (1 / (N : ℝ))) := by
  sorry

end BordenaveCollins
