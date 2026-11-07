-- Prove2me | Theorems.Thm_CompPermOracle_proposition_4_8
-- name    : CompPermOracle.proposition_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:55:19.150208+00:00
-- url     : https://prove2.me/theorems/8b8aea51-36ea-4748-8ca9-48fa1702a634
-- title:
--   Proposition 4.8 — the one-query bound for $V$
-- statement:
--   If $3t+2\le N$, then for every $x\in[N]$,
--   $$
--   \big\|\big(\mathrm{cpO}_x(I_{\mathcal A}\otimes V)-(I_{\mathcal A}\otimes V)P_x\big)(I_{\mathcal A}\otimes\Pi_{\le t})\big\|\le\frac{60}{\sqrt{N-t}}.
--   $$
--   So on low levels, answering a query and then applying $V$ nearly agrees with applying $V$ and then answering a compressed query.
--
--   Differences from the source:
--   - encoding: $[N]=\{1,\dots,N\}$, blank symbol $\bot$ → `Fin N` (0-based), $\bot$ = `none`; reason: a relabelling; no index appears in the bound
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), Proposition 4.8, p.15

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_CompPermOracle_Levels
import Definitions.Def_CompPermOracle_oneQuery

namespace CompPermOracle

/-- Proposition 4.8 (Carolan, Majenz, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), p.15). The norm is the operator norm from `𝒜 ⊗ 𝒫` to `𝒜 ⊗ ℒ`. -/
theorem proposition_4_8 {N t : ℕ} (h : 3 * t + 2 ≤ N) (x : Fin N) :
    ‖queryErr (Vmap N) (cpOAt x) (purP x) t‖ ≤ 60 / Real.sqrt ((N : ℝ) - t) := by sorry

end CompPermOracle
