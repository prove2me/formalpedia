-- Prove2me | Theorems.Thm_ConstrSOSP_proposition_5_3_colour_gaps
-- name    : ConstrSOSP.proposition_5_3_colour_gaps
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:59:58.619713+00:00
-- url     : https://prove2.me/theorems/eedc07ee-baf1-475f-9bfe-8803fdef1d1b
-- title:
--   Proposition 5.3 (iv): the colour functions satisfy (22) for $N\ge10^{40}$
-- statement:
--   Let $N=6\cdot2^n+6\ge10^{40}$ and let $B,M,R,G$ be the values of the blue, black, red and green colour functions at any grid points of $\{0,\dots,N\}^2$.
--
--   **Theorem.** The colour gaps satisfy (22):
--
--   1. $R-M\ge10^{40}$ and $G-R\ge10^{40}$ (Group A);
--   2. $B>10^9$, $9995B\le R-B\le10000B$ and $99B\le M-B\le101B$ (Group B);
--   3. $R-M\ge10^{20}$ (Groups C, F, G);
--   4. $R-B\ge10^{20}$ (Groups D, E).
--
--   This links the abstract group analysis to the actual construction: the gaps occurring in its cells lie in the domains where Proposition 5.3 excludes approximate SOSPs.
--
--   Differences from the source: none.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Proposition 5.3, p.33; (22), p.35; pp.35–36

import Mathlib
import Definitions.Def_ConstrSOSP_gridN
import Definitions.Def_ConstrSOSP_Colour
import Definitions.Def_ConstrSOSP_colourPhi

namespace ConstrSOSP

/-- **Proposition 5.3, the colour gaps** (arXiv:2604.02285, 2 Nov 2026, Proposition 5.3, p.33:
"The color functions of the reduction satisfy (22) for all N ≥ 10^40"; pp.35–36: "For reference
values at any grid corners, Section 5.3 gives 9998N ≤ B ≤ 10000N, 1000000N ≤ M ≤ 1000002N,
99979999N ≤ R ≤ 99980001N, (10^15 − 1)N ≤ G ≤ (10^15 + 1)N. They imply 9995B ≤ R − B ≤ 10000B
and 99B ≤ M − B ≤ 101B, as well as all the lower bounds in (22), for example whenever
N ≥ 10^40.").

Let `N = 6·2ⁿ + 6 ≥ 10⁴⁰`, and let `B`, `M`, `R`, `G` be the values of the blue, black, red and
green colour functions at any grid points of `{0, …, N}²`. Then the gaps satisfy (22):
`R − M ≥ 10⁴⁰`, `G − R ≥ 10⁴⁰` (Group A); `B > 10⁹`, `9995B ≤ R − B ≤ 10000B`,
`99B ≤ M − B ≤ 101B` (Group B); `R − M ≥ 10²⁰` (Groups C, F, G); `R − B ≥ 10²⁰` (Groups D, E). -/
theorem proposition_5_3_colour_gaps (n : ℕ) (hN : 10 ^ 40 ≤ gridN n)
    (aB bB aM bM aR bR aG bG : ℕ) (haB : aB ≤ gridN n) (hbB : bB ≤ gridN n)
    (haM : aM ≤ gridN n) (hbM : bM ≤ gridN n) (haR : aR ≤ gridN n) (hbR : bR ≤ gridN n)
    (haG : aG ≤ gridN n) (hbG : bG ≤ gridN n) :
    let N : ℝ := gridN n
    let B := colourPhi N Colour.blue aB bB
    let M := colourPhi N Colour.black aM bM
    let R := colourPhi N Colour.red aR bR
    let G := colourPhi N Colour.green aG bG
    10 ^ 40 ≤ R - M ∧ 10 ^ 40 ≤ G - R ∧
      10 ^ 9 < B ∧ 9995 * B ≤ R - B ∧ R - B ≤ 10000 * B ∧ 99 * B ≤ M - B ∧ M - B ≤ 101 * B ∧
      10 ^ 20 ≤ R - M ∧ 10 ^ 20 ≤ R - B := by sorry

end ConstrSOSP
