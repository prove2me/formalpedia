-- Prove2me | Theorems.Thm_AvgPHETH_s2_form
-- name    : AvgPHETH.s2_form
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:37:18.807967+00:00
-- url     : https://prove2.me/theorems/df080d19-b8bb-4660-92b7-d799688e8639
-- title:
--   Proof of Theorem 1.2 (i) — $L\in\mathrm S_2^k\mathrm{TIME}^O[2^{O(w/\log^kw)}]$
-- statement:
--   Suppose $\Sigma_d^{p,O}\times\{\mathcal U,\mathcal T\}\subseteq\mathrm{AvgP}^O$ for an oracle $O$ and a fixed $d\ge2$, let $1\le k<d$, and let $L\in\Sigma_d^{p,O}$ have witness length $w\ge n^{\Omega(1)}$. Then
--
--   $$L\in\mathrm S_2^k\mathrm{TIME}^O\left[2^{O(w/\log^kw)}\right].$$
--
--   This is the display obtained by $k$ applications of Lemma 6.1 at scale $w$, before the removal of the symmetric alternations by Lemma 6.5.
--
--   Differences from the source:
--   - reading: the move lengths of a witness are not said to be computable → each move length is polynomial-time computable; reason: Lemma 6.1 and the padding step on p.29 use it, and without it the language can be undecidable
--   - encoding: $2^{O(w/\log^kw)}$ → $\lceil2^{cw/(\log_2\max(w,2))^k}\rceil$; reason: $\max(w,2)$ only excludes $w\le1$, and the constant is named $c$
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), proof of Theorem 1.2 (i), p.30 (PDF 32)

import Mathlib
import Definitions.Def_AvgPHETH_TimesUT
import Definitions.Def_AvgPHETH_SigmaPO
import Definitions.Def_AvgPHETH_S2kTIME
import Definitions.Def_AvgPHETH_HasWitnessLength
import Definitions.Def_AvgPHETH_PolyLower
import Definitions.Def_AvgPHETH_witnessTime

namespace AvgPHETH

/-- **The `S₂` form**, the display in the proof of Theorem 1.2 (i) (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), p.30 (PDF 32)): for `d ≥ 2`, `1 ≤ k < d` and `L ∈ Σ_d^{p,O}` with witness length `w ≥ n^{Ω(1)}`, if
`Σ_d^{p,O} × {U, T} ⊆ AvgP^O` then "the `k` applications give `k` nested `S₂` operators, and hence" `L ∈ S₂^kTIME^O[2^{O(w/log^k w)}]`. -/
theorem s2_form (O : Set (List Bool)) (d k : ℕ) (w : ℕ → ℕ) (L : Set (List Bool)) (hd : 2 ≤ d)
    (hk1 : 1 ≤ k) (hkd : k < d) (hAvg : TimesUT O (SigmaPO O d))
    (hL : HasWitnessLength O d L w) (hw : PolyLower w) :
    ∃ c : ℕ, S2kTIME O k (witnessTime c k w) L := by sorry

end AvgPHETH
