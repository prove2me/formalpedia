-- Prove2me | Theorems.Thm_CompPermOracle_lemma_4_15
-- name    : CompPermOracle.lemma_4_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:55:44.283844+00:00
-- url     : https://prove2.me/theorems/e0658dde-8515-4e3f-8d29-043d821058bf
-- title:
--   Lemma 4.15 — square-function bound for $h^0$
-- statement:
--   If $3r+2\le N$ and $m=N-r$, then for each $x\in[N]$,
--   $$
--   \mathrm{Col}(h^0_{\cdot,r})^2,\ \mathrm{Row}(h^0_{\cdot,r})^2\le\frac{32}{m}.
--   $$
--   This is the bound (24) of Proposition 4.7.
--
--   Differences from the source:
--   - encoding: $h^0_{y,r}$ on $\mathcal H_r$ → precomposed with $\Pi_r$, as operators on $\mathcal P$; reason: the same $\mathrm{Col}$ and $\mathrm{Row}$
--   - encoding: $[N]=\{1,\dots,N\}$, blank symbol $\bot$ → `Fin N` (0-based), $\bot$ = `none`; reason: a relabelling; no index appears in the bound
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), Lemma 4.15, p.23

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_CompPermOracle_Levels
import Definitions.Def_CompPermOracle_oneQuery

namespace CompPermOracle

/-- Lemma 4.15 (Carolan, Majenz, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), p.23), with `m = N − r` and `x` fixed but arbitrary. -/
theorem lemma_4_15 {N r : ℕ} (h : 3 * r + 2 ≤ N) (x : Fin N) :
    Col (fun y => hZero x y r) ^ 2 ≤ 32 / ((N : ℝ) - r) ∧
    Row (fun y => hZero x y r) ^ 2 ≤ 32 / ((N : ℝ) - r) := by sorry

end CompPermOracle
