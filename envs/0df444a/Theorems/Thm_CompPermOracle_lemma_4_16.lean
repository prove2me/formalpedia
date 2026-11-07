-- Prove2me | Theorems.Thm_CompPermOracle_lemma_4_16
-- name    : CompPermOracle.lemma_4_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:55:04.589913+00:00
-- url     : https://prove2.me/theorems/73d8fe83-4845-42a0-98d6-708d8b0c51f4
-- title:
--   Lemma 4.16 — square-function bound for $h^-$
-- statement:
--   If $3r+2\le N$ and $m=N-r$, then for each $x\in[N]$,
--   $$
--   \mathrm{Col}(h^-_{\cdot,r})^2,\ \mathrm{Row}(h^-_{\cdot,r})^2\le\frac{24}{m}.
--   $$
--   At $r=0$ the family is zero by convention. This is the bound (25) of Proposition 4.7.
--
--   Differences from the source:
--   - encoding: $h^-_{y,r}$ on $\mathcal H_r$; omitted at $r=0$ → precomposed with $\Pi_r$, as operators on $\mathcal P$; the zero map at $r=0$; reason: the convention of p.14; the same $\mathrm{Col}$ and $\mathrm{Row}$
--   - encoding: $[N]=\{1,\dots,N\}$, blank symbol $\bot$ → `Fin N` (0-based), $\bot$ = `none`; reason: a relabelling; no index appears in the bound
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), Lemma 4.16, p.25

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_CompPermOracle_Levels
import Definitions.Def_CompPermOracle_oneQuery

namespace CompPermOracle

/-- Lemma 4.16 (Carolan, Majenz, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), p.25), with `m = N − r` and `x` fixed but arbitrary. At `r = 0`
the family `h⁻` is zero by the convention of p.14. -/
theorem lemma_4_16 {N r : ℕ} (h : 3 * r + 2 ≤ N) (x : Fin N) :
    Col (fun y => hMinus x y r) ^ 2 ≤ 24 / ((N : ℝ) - r) ∧
    Row (fun y => hMinus x y r) ^ 2 ≤ 24 / ((N : ℝ) - r) := by sorry

end CompPermOracle
