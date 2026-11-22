-- Prove2me | Theorems.Thm_AvgPHETH_Supplement_theorem_1_2_ii
-- name    : AvgPHETH.Supplement.theorem_1_2_ii
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T05:00:06.273473+00:00
-- url     : https://prove2.me/theorems/fce5f6e7-5c4d-407e-91a3-9e9cf3466c86
-- title:
--   Theorem 1.2 (ii) — $L\in\mathrm{DTIME}^{\Sigma_k^{p,O}}[2^{O(n/\log^{k+1}n)}]$ under $\mathrm{Dist}\Sigma_{d+1}^{p,O}\subseteq\mathrm{AvgP}^O$
-- statement:
--   Let $O$ be an oracle and $d,k\ge0$. Suppose $\mathrm{Dist}\Sigma_{d+1}^{p,O}\subseteq\mathrm{AvgP}^O$. Then every language $L\in\Sigma_d^{p,O}$ can be solved by a deterministic algorithm with a $\Sigma_k^{p,O}$ oracle in time
--
--   $$2^{O(n/\log^{k+1}n)},$$
--
--   where $n$ denotes the input length.
--
--   Each level of alternation available to the simulating algorithm saves one logarithmic factor in the exponent, measured in the input length. The case $k=0$, without an oracle, is a result of Hirahara (2021). By Theorem 1.5 the bound cannot be improved by relativizing techniques.
--
--   Differences from the source:
--   - generalization: under $\mathrm{DistPH}\subseteq\mathrm{AvgP}$, with no oracle, for every $L\in\mathrm{PH}$ → every oracle $O$ and every $d$, under $\mathrm{Dist}\Sigma_{d+1}^{p,O}\subseteq\mathrm{AvgP}^O$, for every $L\in\Sigma_d^{p,O}$; reason: the refinement on p.3 ("Theorem 1.2 (ii) only requires $\mathrm{Dist}\Sigma_{d+1}^p\subseteq\mathrm{AvgP}$") and the relativized proof on p.30; at $O=\emptyset$, with $d$ such that $L\in\Sigma_d^p$, $\mathrm{DistPH}\subseteq\mathrm{AvgP}$ gives the hypothesis
--   - encoding: time $2^{O(n/\log^{k+1}n)}$ → $\lceil2^{cn/(\log_2\max(n,2))^{k+1}}\rceil+c$ for one natural $c$ chosen after $O,d,k,L$ (published witnessTime); reason: $\max(n,2)$ only excludes $n\le1$, where the logarithm is $0$; the summand only matters for small $n$
--   - encoding: deterministic algorithms with a $\Sigma_k^{p,O}$ oracle → the published DTimeOracle: one oracle language in SigmaPO O k, two-tape machines KarpLiptonOM.OracleTM; the oracle $\emptyset$ means no oracle; reason: the base mission's conventions; same classes up to polynomial overhead
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Theorem 1.2 (ii), p.3 (PDF 5), with the refinement on p.3 and the proof on p.30 (PDF 32)

import Mathlib
import Definitions.Def_AvgPHETH_DistSubAvgP
import Definitions.Def_AvgPHETH_SigmaPO
import Definitions.Def_AvgPHETH_DTimeOracle
import Definitions.Def_AvgPHETH_witnessTime

namespace AvgPHETH.Supplement

open AvgPHETH

/-- **Theorem 1.2 (ii)** (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), p.3 (PDF 5)), in the refined relativized form of p.3 ("for
`L ∈ Σ_d^p`, … Theorem 1.2 (ii) only requires `DistΣ_{d+1}^p ⊆ AvgP`") and of its proof on p.30
(PDF 32): for every oracle `O` and all `d, k ≥ 0`, if `DistΣ_{d+1}^{p,O} ⊆ AvgP^O`, then every
`L ∈ Σ_d^{p,O}` is solved by a deterministic algorithm with a `Σ_k^{p,O}` oracle in time
`2^{O(n/log^{k+1} n)}`.

**Formalization Note** `2^{O(n/log^{k+1} n)}` is `⌈2^{c n/(log₂ max(n,2))^{k+1}}⌉ + c` (the published
`witnessTime c (k+1) id`) for a constant `c` chosen after `O, d, k, L`; the summand `c` is for small
`n`. -/
theorem theorem_1_2_ii (O : Set (List Bool)) (d k : ℕ) (L : Set (List Bool))
    (hAvg : DistSubAvgP O (d + 1)) (hL : L ∈ SigmaPO O d) :
    ∃ c : ℕ, DTimeOracle (SigmaPO O k) (fun n => witnessTime c (k + 1) id n + c) L := by sorry

end AvgPHETH.Supplement
