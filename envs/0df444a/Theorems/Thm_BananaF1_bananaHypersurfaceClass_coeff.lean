-- Prove2me | Theorems.Thm_BananaF1_bananaHypersurfaceClass_coeff
-- name    : BananaF1.bananaHypersurfaceClass_coeff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T16:41:51.210044+00:00
-- url     : https://prove2.me/theorems/12b5ce33-61d7-403c-913e-943f118c568f
-- title:
--   Coefficients of $[X_{\Gamma_n}]$ in the variable $\mathbb{T}$
-- statement:
--   The closed form of the coefficients of the class $[X_{\Gamma_n}]$ of equation (3.8), for $n \ge 3$. Writing $[X_{\Gamma_n}] = \sum_{k \ge 0} a_k \mathbb{T}^k$, the statement is
--
--   $$a_k \;=\; \begin{cases} \binom{n}{k+1} - (-1)^{\,n-1-k} - n, & k = n-2,\\[2pt] \binom{n}{k+1} - (-1)^{\,n-1-k}, & k < n,\ k \neq n-2,\\[2pt] 0, & k \ge n. \end{cases}$$
--
--   The three summands of (3.8) contribute in order: the binomial coefficient comes from $[\mathbb{P}^{n-1}]$, the sign from the alternating quotient, and the extra $n$ from the term $n\,\mathbb{T}^{n-2}$. For $n = 15$ this reproduces the expansion printed in the source, $14 + 106\,\mathbb{T} + 454\,\mathbb{T}^2 + \cdots + 104\,\mathbb{T}^{12} + \mathbb{T}^{13}$.
-- source:
--   D. Bejleri, M. Marcolli, Quantum field theory over F_1, Journal of Geometry and Physics (2013), doi:10.1016/j.geomphys.2013.03.002 (https://doi.org/10.1016/j.geomphys.2013.03.002); Section 3.6, Lemma 3.9 together with equations (3.8), (3.9), (3.10), and the necessary conditions of Section 3.3 Proposition 3.1 and Section 3.5 Lemma 3.8. The closed formula (3.8) is Theorem 3.10 of P. Aluffi, M. Marcolli, Feynman motives of banana graphs, Commun. Number Theory Phys. 3 (2009), no. 1, 1-57, and the complement formula is Corollary 3.13 there.

import Definitions.Def_bananaF1Classes
open Polynomial

namespace BananaF1

theorem bananaHypersurfaceClass_coeff (n k : ℕ) (hn : 3 ≤ n) :
    (bananaHypersurfaceClass n).coeff k =
      (if k < n then (n.choose (k + 1) : ℤ) - (-1 : ℤ) ^ (n - 1 - k) else 0)
        - (if k = n - 2 then (n : ℤ) else 0) := by sorry

end BananaF1
