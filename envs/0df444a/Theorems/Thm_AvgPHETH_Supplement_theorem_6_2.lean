-- Prove2me | Theorems.Thm_AvgPHETH_Supplement_theorem_6_2
-- name    : AvgPHETH.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T05:01:04.851921+00:00
-- url     : https://prove2.me/theorems/1ee3004e-4a87-43a4-90ef-bdc1822f4a6e
-- title:
--   Theorem 6.2 — $\Sigma_d^{p,O}\subseteq\mathrm S_2^k\mathrm{TIME}^O[2^{O(n/\log^{k+1}n)}]$
-- statement:
--   Suppose $\mathrm{Dist}\Sigma_{d+1}^{p,O}\subseteq\mathrm{AvgP}^O$ for an oracle $O$ and a fixed $d\ge1$. Then, for every $k\ge0$,
--
--   $$\Sigma_d^{p,O}\subseteq\mathrm S_2^k\mathrm{TIME}^O\big[2^{O(n/\log^{k+1}n)}\big].$$
--
--   Each additional symmetric-alternation operator $\mathrm S_2$ saves a logarithmic factor in the exponent. With Lemma 6.5 this gives Theorem 1.2 (ii).
--
--   Differences from the source:
--   - encoding: $2^{O(n/\log^{k+1}n)}$ → witnessTime c (k+1) id, i.e. $\lceil2^{cn/(\log_2\max(n,2))^{k+1}}\rceil$, with a natural $c$ chosen after $L$; reason: $\max(n,2)$ only excludes $n\le1$; the published S2kTIME already allows a constant factor and summand
--   - encoding: $\mathrm S_2^k\mathrm{TIME}^O[\cdot]$ of §4.2 → the published AvgPHETH.S2kTIME; reason: the base mission's definition of the same class
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Theorem 6.2, p.26 (PDF 28)

import Mathlib
import Definitions.Def_AvgPHETH_DistSubAvgP
import Definitions.Def_AvgPHETH_SigmaPO
import Definitions.Def_AvgPHETH_S2kTIME
import Definitions.Def_AvgPHETH_witnessTime

namespace AvgPHETH.Supplement

open AvgPHETH

/-- **Theorem 6.2** (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), p.26 (PDF 28)): suppose `DistΣ_{d+1}^{p,O} ⊆ AvgP^O` for an oracle `O` and a
fixed `d ≥ 1`. Then, for every `k ≥ 0`, `Σ_d^{p,O} ⊆ S₂^kTIME^O[2^{O(n/log^{k+1} n)}]`.

**Formalization Note** `S₂^kTIME^O[·]` is the published `AvgPHETH.S2kTIME` (which already allows a
constant factor and summand); `2^{O(n/log^{k+1} n)}` is `witnessTime c (k+1) id`, i.e.
`⌈2^{c n/(log₂ max(n,2))^{k+1}}⌉`, for a constant `c` chosen after `L`. -/
theorem theorem_6_2 (O : Set (List Bool)) (d : ℕ) (hd : 1 ≤ d) (hAvg : DistSubAvgP O (d + 1))
    (k : ℕ) (L : Set (List Bool)) (hL : L ∈ SigmaPO O d) :
    ∃ c : ℕ, S2kTIME O k (witnessTime c (k + 1) id) L := by sorry

end AvgPHETH.Supplement
