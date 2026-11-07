-- Prove2me | Theorems.Thm_AvgPHETH_theorem_1_2_i
-- name    : AvgPHETH.theorem_1_2_i
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:37:23.731759+00:00
-- url     : https://prove2.me/theorems/0c19018d-ac1c-4d8f-b2fd-e30a3d5ac7fb
-- title:
--   Theorem 1.2 (i) — $L\in\mathrm{DTIME}^{\Sigma_k^{p,O}}[2^{O(w/\log^kw)}]$, refined form of p.30
-- statement:
--   For every oracle $O$ and every fixed $d\ge2$, suppose $\Sigma_d^{p,O}\times\{\mathcal U,\mathcal T\}\subseteq\mathrm{AvgP}^O$. Then, for every $k\ge0$, every $L\in\Sigma_d^{p,O}$ with witness length $w\ge n^{\Omega(1)}$ can be solved by a deterministic algorithm with a $\Sigma_k^{p,O}$ oracle in time $2^{O(w/\log^kw)}$.
--
--   Each level of alternation available to the simulating algorithm saves a logarithmic factor in the exponent, measured in the witness length rather than the input length.
--
--   Differences from the source:
--   - generalization: under $\mathrm{DistPH}\subseteq\mathrm{AvgP}$, with no oracle, for $L\in\mathrm{PH}$ → the paragraph of p.30: every oracle $O$, fixed $d\ge2$, $\Sigma_d^{p,O}\times\{\mathcal U,\mathcal T\}\subseteq\mathrm{AvgP}^O$; reason: at $O=\emptyset$ the footnote on p.10 gives the hypothesis, and a move of length $0$ makes a $\Sigma_1$ language a $\Sigma_2$ one, so $d\ge2$ loses nothing
--   - reading: the move lengths of a witness are not said to be computable → each move length is polynomial-time computable; reason: Lemma 6.1 and the padding step on p.29 use it, and without it the language can be undecidable
--   - encoding: time $2^{O(w/\log^kw)}$ → $\lceil2^{cw/(\log_2\max(w,2))^k}\rceil+c$; reason: $\max(w,2)$ only excludes $w\le1$, and the summand only matters for small $n$
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Theorem 1.2 (i), p.3 (PDF 5), in the refined form of p.30 (PDF 32)

import Mathlib
import Definitions.Def_AvgPHETH_TimesUT
import Definitions.Def_AvgPHETH_SigmaPO
import Definitions.Def_AvgPHETH_DTimeOracle
import Definitions.Def_AvgPHETH_HasWitnessLength
import Definitions.Def_AvgPHETH_PolyLower
import Definitions.Def_AvgPHETH_witnessTime

namespace AvgPHETH

/-- **Theorem 1.2 (i)** (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), p.3 (PDF 5)), in the refined form of p.30 (PDF 32): for every oracle `O` and every fixed `d ≥ 2`, under `Σ_d^{p,O} × {U, T} ⊆ AvgP^O`, for every `k ≥ 0` every `L ∈ Σ_d^{p,O}` with
witness length `w ≥ n^{Ω(1)}` is solved by a deterministic algorithm with a `Σ_k^{p,O}` oracle in time `2^{O(w/log^k w)}`.

**Formalization Note** The summand `c` is for small `n`, where the power alone can be a single step. -/
theorem theorem_1_2_i (O : Set (List Bool)) (d k : ℕ) (w : ℕ → ℕ) (L : Set (List Bool))
    (hd : 2 ≤ d) (hAvg : TimesUT O (SigmaPO O d)) (hL : HasWitnessLength O d L w)
    (hw : PolyLower w) :
    ∃ c : ℕ, DTimeOracle (SigmaPO O k) (fun n => witnessTime c k w n + c) L := by sorry

end AvgPHETH
