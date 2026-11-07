-- Prove2me | Theorems.Thm_CompPermOracle_proposition_4_7
-- name    : CompPermOracle.proposition_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:54:46.242524+00:00
-- url     : https://prove2.me/theorems/f48c2717-e7e4-410d-8eba-7ac92fb05b28
-- title:
--   Proposition 4.7 — the three square-function bounds
-- statement:
--   If $3r+2\le N$ and $m=N-r$, then for each $x\in[N]$,
--   $$
--   \mathrm{Col}(z^+_{\cdot,r}\oplus z^0_{\cdot,r})^2,\ \mathrm{Row}(z^+_{\cdot,r}\oplus z^0_{\cdot,r})^2\le\frac{64}{m},
--   $$
--   $$
--   \mathrm{Col}(h^0_{\cdot,r})^2,\ \mathrm{Row}(h^0_{\cdot,r})^2\le\frac{32}{m},\qquad\mathrm{Col}(h^-_{\cdot,r})^2,\ \mathrm{Row}(h^-_{\cdot,r})^2\le\frac{24}{m}.
--   $$
--   These are the core one-query inequalities of the source.
--
--   Differences from the source:
--   - encoding: the family $z^+_{\cdot,r}\oplus z^0_{\cdot,r}$ into $\mathcal L_{r+1}\oplus\mathcal L_r$ → the sum $z^+_{y,r}+z^0_{y,r}$ in $\mathcal L$; reason: orthogonal levels, so an isometric embedding; the same $\mathrm{Col}$ and $\mathrm{Row}$
--   - encoding: $[N]=\{1,\dots,N\}$, blank symbol $\bot$ → `Fin N` (0-based), $\bot$ = `none`; reason: a relabelling; no index appears in the bound
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), Proposition 4.7, p.14

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_CompPermOracle_Levels
import Definitions.Def_CompPermOracle_oneQuery

namespace CompPermOracle

/-- Proposition 4.7 (Carolan, Majenz, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), p.14): eqs. (23), (24), (25), with `m = N − r` and `x` fixed
but arbitrary (the preamble of §4.2). -/
theorem proposition_4_7 {N r : ℕ} (h : 3 * r + 2 ≤ N) (x : Fin N) :
    Col (fun y => zSum x y r) ^ 2 ≤ 64 / ((N : ℝ) - r) ∧
    Row (fun y => zSum x y r) ^ 2 ≤ 64 / ((N : ℝ) - r) ∧
    Col (fun y => hZero x y r) ^ 2 ≤ 32 / ((N : ℝ) - r) ∧
    Row (fun y => hZero x y r) ^ 2 ≤ 32 / ((N : ℝ) - r) ∧
    Col (fun y => hMinus x y r) ^ 2 ≤ 24 / ((N : ℝ) - r) ∧
    Row (fun y => hMinus x y r) ^ 2 ≤ 24 / ((N : ℝ) - r) := by sorry

end CompPermOracle
