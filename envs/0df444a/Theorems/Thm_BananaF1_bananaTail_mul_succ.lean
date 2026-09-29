-- Prove2me | Theorems.Thm_BananaF1_bananaTail_mul_succ
-- name    : BananaF1.bananaTail_mul_succ
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T16:28:59.888378+00:00
-- url     : https://prove2.me/theorems/13d545b2-da8b-4044-9461-7006fcf0c13d
-- title:
--   Equation (3.10): $(\mathbb{T}+1)\sum_{j<n}(-1)^{n-1-j}\mathbb{T}^j = \mathbb{T}^n - (-1)^n$
-- statement:
--   Equation (3.10) of the source, as a polynomial identity in $\mathbb{Z}[\mathbb{T}]$: for every $n \ge 1$,
--
--   $$(\mathbb{T}+1) \cdot \sum_{j=0}^{n-1} (-1)^{\,n-1-j}\, \mathbb{T}^{j} \;=\; \mathbb{T}^n - (-1)^n .$$
--
--   It identifies the alternating polynomial $\mathbb{T}^{n-1} - \mathbb{T}^{n-2} + \cdots \pm 1$ as the exact quotient $(\mathbb{T}^n - (-1)^n)/(\mathbb{T}+1)$, which is the second summand of the closed formula (3.8) for $[X_{\Gamma_n}]$ and the main part of the complement class $[Y_{\Gamma_n}]$.
-- source:
--   D. Bejleri, M. Marcolli, Quantum field theory over F_1, Journal of Geometry and Physics (2013), doi:10.1016/j.geomphys.2013.03.002 (https://doi.org/10.1016/j.geomphys.2013.03.002); Section 3.6, Lemma 3.9 together with equations (3.8), (3.9), (3.10), and the necessary conditions of Section 3.3 Proposition 3.1 and Section 3.5 Lemma 3.8. The closed formula (3.8) is Theorem 3.10 of P. Aluffi, M. Marcolli, Feynman motives of banana graphs, Commun. Number Theory Phys. 3 (2009), no. 1, 1-57, and the complement formula is Corollary 3.13 there.

import Definitions.Def_bananaF1Classes
open Polynomial

namespace BananaF1

theorem bananaTail_mul_succ (n : ℕ) (hn : 1 ≤ n) :
    (X + 1) * bananaTail n = X ^ n - C ((-1 : ℤ) ^ n) := by sorry

end BananaF1
