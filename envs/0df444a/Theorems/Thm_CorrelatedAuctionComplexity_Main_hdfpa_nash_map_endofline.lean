-- Prove2me | Theorems.Thm_CorrelatedAuctionComplexity_Main_hdfpa_nash_map_endofline
-- name    : CorrelatedAuctionComplexity.Main.hdfpa_nash_map_endofline
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T07:13:22.957628+00:00
-- url     : https://prove2.me/theorems/bc6fd923-daff-4a7b-a82f-765162ed168d
-- title:
--   Lemma 16 — End-of-Line reduction for the polynomially continuous Nash map
-- statement:
--   Assume the uniform polynomial-time exact expected-utility algorithm of Lemma 15. Then finding a rational weak approximate fixed point of the HDFPA Nash map reduces by a polynomial-time search reduction to the concrete circuit-defined End-of-Line problem.
--
--   The reduction implements [EY10, Proposition 2.2] on the no-overbidding product simplex. Expected utilities and pure-deviation utilities are computed exactly as rationals, so the gains and normalized Nash map are polynomially computable. If $\|\sigma-\tau\|_\infty\le\xi$, the source's total-variation estimates give, for normalized payoffs,
--   $$
--   |\bar U_i(\sigma)-\bar U_i(\tau)|\le \frac{n|B|\xi}{2},
--   \qquad
--   |\bar U_i(a,\sigma_{-i})-\bar U_i(a,\tau_{-i})|\le \frac{n|B|\xi}{2},
--   $$
--   hence a gain change of at most $n|B|\xi$ and the Nash-map Lipschitz bound
--   $$
--   |F_H(\sigma)_{i,b}-F_H(\tau)_{i,b}|\le 4n|B|^2\xi.
--   $$
--   Thus the map is polynomially continuous, and an End-of-Line endpoint decodes to a rational profile within the prescribed weak fixed-point tolerance and polynomial witness bound.
--
--   **Formalization Note** The conclusion is a full Cook-machine search reduction, including construction of a well-formed End-of-Line instance, polynomial-time answer decoding, and correctness for every endpoint. `ExpectedUtilityPolytime` is exactly the theorem proved by Lemma 15.
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), proof of Lemma 16, pp. 20–21: polynomial computability and polynomial continuity of Nash's map, followed by [EY10, Proposition 2.2]; Lemma 15, pp. 19–20, supplies exact polynomial-time utilities.

import Definitions.Def_CorrelatedAuctionComplexity_Main_NashFixedSearch

set_option autoImplicit false

theorem CorrelatedAuctionComplexity.Main.hdfpa_nash_map_endofline :
    ExpectedUtilityPolytime →
      CardinalMatching.SearchReduces hNashFixedSearch EndOfLine := by sorry
