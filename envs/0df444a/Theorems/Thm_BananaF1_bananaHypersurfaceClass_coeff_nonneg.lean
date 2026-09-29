-- Prove2me | Theorems.Thm_BananaF1_bananaHypersurfaceClass_coeff_nonneg
-- name    : BananaF1.bananaHypersurfaceClass_coeff_nonneg
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T16:48:27.438723+00:00
-- url     : https://prove2.me/theorems/ba7babc8-76f4-42a3-b121-2e4ac5616d3b
-- title:
--   Lemma 3.9 (first half): all coefficients of $[X_{\Gamma_n}]$ are non-negative
-- statement:
--   **Goal of the mission.** The first half of Lemma 3.9: for every $n \ge 3$, the class of the banana graph hypersurface,
--
--   $$[X_{\Gamma_n}] \;=\; \frac{(1+\mathbb{T})^n - 1}{\mathbb{T}} - \frac{\mathbb{T}^n - (-1)^n}{\mathbb{T}+1} - n\,\mathbb{T}^{n-2},$$
--
--   written in the variable $\mathbb{T} = [\mathbb{G}_m] = \mathbb{L} - 1$, has **non-negative** coefficients in every degree: $[X_{\Gamma_n}] = \sum_{k\ge 0} a_k \mathbb{T}^k$ with $a_k \ge 0$ for all $k$.
--
--   This is the necessary condition of Lemma 3.8 for the existence of an $\mathbb{F}_1$-structure: a variety with a torification by tori $\mathbb{G}_m^{d_i}$ has class $\sum_i \mathbb{T}^{d_i}$, hence non-negative coefficients. Although the closed formula appears at first to contain negative coefficients, the binomial terms dominate the subtracted alternating tail in every degree. The companion statement about $[Y_{\Gamma_n}]$ shows the condition is not automatic: the complement class does have a negative coefficient.
-- source:
--   D. Bejleri, M. Marcolli, Quantum field theory over F_1, Journal of Geometry and Physics (2013), doi:10.1016/j.geomphys.2013.03.002 (https://doi.org/10.1016/j.geomphys.2013.03.002); Section 3.6, Lemma 3.9 together with equations (3.8), (3.9), (3.10), and the necessary conditions of Section 3.3 Proposition 3.1 and Section 3.5 Lemma 3.8. The closed formula (3.8) is Theorem 3.10 of P. Aluffi, M. Marcolli, Feynman motives of banana graphs, Commun. Number Theory Phys. 3 (2009), no. 1, 1-57, and the complement formula is Corollary 3.13 there.

import Definitions.Def_bananaF1Classes
open Polynomial

namespace BananaF1

theorem bananaHypersurfaceClass_coeff_nonneg (n : ℕ) (hn : 3 ≤ n) (k : ℕ) :
    0 ≤ (bananaHypersurfaceClass n).coeff k := by sorry

end BananaF1
