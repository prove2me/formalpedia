-- Prove2me | Theorems.Thm_BananaF1_bananaHypersurfaceClass_coeff_zero
-- name    : BananaF1.bananaHypersurfaceClass_coeff_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T16:47:34.686102+00:00
-- url     : https://prove2.me/theorems/0881374e-cc52-4d93-a81c-17bc08b5a401
-- title:
--   Constant term of $[X_{\Gamma_n}]$: the Euler-characteristic condition
-- statement:
--   For $n \ge 3$ the constant term of $[X_{\Gamma_n}]$, written in the variable $\mathbb{T} = \mathbb{L} - 1$, equals $n + (-1)^n$; that is, $n+1$ for even $n$ and $n-1$ for odd $n$ (for instance $14$ when $n = 15$, matching the expansion printed in the source).
--
--   As the source notes after Lemma 3.8, for a class written as $\sum_k a_k \mathbb{T}^k$ the constant term $a_0$ is the Euler characteristic, since positive-dimensional tori have vanishing Euler characteristic. The value $n + (-1)^n$ is positive for $n \ge 3$, so the necessary condition $\chi \ge 0$ of Proposition 3.1 holds for the banana graph hypersurfaces. The formal statement asserts only the equality of integers.
-- source:
--   D. Bejleri, M. Marcolli, Quantum field theory over F_1, Journal of Geometry and Physics (2013), doi:10.1016/j.geomphys.2013.03.002 (https://doi.org/10.1016/j.geomphys.2013.03.002); Section 3.6, Lemma 3.9 together with equations (3.8), (3.9), (3.10), and the necessary conditions of Section 3.3 Proposition 3.1 and Section 3.5 Lemma 3.8. The closed formula (3.8) is Theorem 3.10 of P. Aluffi, M. Marcolli, Feynman motives of banana graphs, Commun. Number Theory Phys. 3 (2009), no. 1, 1-57, and the complement formula is Corollary 3.13 there.

import Definitions.Def_bananaF1Classes
open Polynomial

namespace BananaF1

theorem bananaHypersurfaceClass_coeff_zero (n : ℕ) (hn : 3 ≤ n) :
    (bananaHypersurfaceClass n).coeff 0 = (n : ℤ) + (-1 : ℤ) ^ n := by sorry

end BananaF1
