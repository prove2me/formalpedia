-- Prove2me | Theorems.Thm_BananaF1_bananaProj_mul_X
-- name    : BananaF1.bananaProj_mul_X
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T16:24:18.51755+00:00
-- url     : https://prove2.me/theorems/bdd738a4-3edd-422f-9efc-0152271531fb
-- title:
--   Equation (3.9): $\mathbb{T}\,[\mathbb{P}^{n-1}] = (1+\mathbb{T})^n - 1$
-- statement:
--   Equation (3.9) of the source, as a polynomial identity in $\mathbb{Z}[\mathbb{T}]$: for every $n \in \mathbb{N}$,
--
--   $$\mathbb{T} \cdot \sum_{k=1}^{n} \binom{n}{k} \mathbb{T}^{k-1} \;=\; (1+\mathbb{T})^n - 1 .$$
--
--   This is what justifies calling $\sum_{k=1}^{n} \binom{n}{k}\mathbb{T}^{k-1}$ the class $[\mathbb{P}^{n-1}]$ written as $((1+\mathbb{T})^n-1)/\mathbb{T}$: the division is exact, with the displayed polynomial as quotient. No hypothesis on $n$ is needed; for $n = 0$ both sides vanish.
-- source:
--   D. Bejleri, M. Marcolli, Quantum field theory over F_1, Journal of Geometry and Physics (2013), doi:10.1016/j.geomphys.2013.03.002 (https://doi.org/10.1016/j.geomphys.2013.03.002); Section 3.6, Lemma 3.9 together with equations (3.8), (3.9), (3.10), and the necessary conditions of Section 3.3 Proposition 3.1 and Section 3.5 Lemma 3.8. The closed formula (3.8) is Theorem 3.10 of P. Aluffi, M. Marcolli, Feynman motives of banana graphs, Commun. Number Theory Phys. 3 (2009), no. 1, 1-57, and the complement formula is Corollary 3.13 there.

import Definitions.Def_bananaF1Classes
open Polynomial

namespace BananaF1

theorem bananaProj_mul_X (n : ℕ) :
    X * bananaProjClass n = (1 + X : Polynomial ℤ) ^ n - 1 := by sorry

end BananaF1
