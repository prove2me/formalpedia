-- Prove2me | Theorems.Thm_CompPermOracle_lemma_4_12
-- name    : CompPermOracle.lemma_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:53:45.563557+00:00
-- url     : https://prove2.me/theorems/1851b4d5-610d-4000-b49d-028fdcecfca6
-- title:
--   Lemma 4.12 — the downward component stays in the frame range
-- statement:
--   If $3r+2\le N$, then for every $a\in K_r$ and all $x,y\in[N]$, $L_{r-1}M_{x,y}a\in K_{r-1}$. The statement is vacuous for $r=0$.
--
--   **Formalization Note** This is the convention of §4.4 from p.20 on: the input is $a\in K_r$, with no $V_r$.
--
--   Differences from the source:
--   - encoding: vacuous for $r=0$ → hypothesis `1 ≤ r`, with `r - 1` an exact subtraction; reason: the same statement
--   - encoding: $[N]=\{1,\dots,N\}$, blank symbol $\bot$ → `Fin N` (0-based), $\bot$ = `none`; reason: a relabelling; no index appears in the bound
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), Lemma 4.12, p.20

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_CompPermOracle_Levels

namespace CompPermOracle

/-- Lemma 4.12 (Carolan, Majenz, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), p.20), in the convention of §4.4: `b⁻_y = L_{r−1} M_y a` for
`a ∈ K_r`, with no `V_r`.

**Formalization Note.** "The statement is vacuous for `r = 0`" is the hypothesis `1 ≤ r`, which makes
`r - 1` an exact natural subtraction. -/
theorem lemma_4_12 {N r : ℕ} (hr : 1 ≤ r) (h : 3 * r + 2 ≤ N) (x y : Fin N)
    {a : Hil (PartialPerm N)} (ha : a ∈ Kr N r) :
    Lproj N (r - 1) (compM x y a) ∈ Kr N (r - 1) := by sorry

end CompPermOracle
