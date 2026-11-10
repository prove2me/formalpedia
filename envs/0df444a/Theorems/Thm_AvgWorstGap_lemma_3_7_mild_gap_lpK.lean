-- Prove2me | Theorems.Thm_AvgWorstGap_lemma_3_7_mild_gap_lpK
-- name    : AvgWorstGap.lemma_3_7_mild_gap_lpK
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:52:37.252054+00:00
-- url     : https://prove2.me/theorems/383a4ad0-a508-4c95-9348-77c50c4cf45d
-- title:
--   Lemma 3.7 — from Mild-Gap-MINpKT^O to Mild-Gap-MINℓ-pKT^O
-- statement:
--   For every oracle $O$: if $\mathrm{Mild}\text{-}\mathrm{Gap}\text{-}\mathrm{MINpKT}^O\in\mathsf{prBPP}$, then $\mathrm{Mild}\text{-}\mathrm{Gap}\text{-}\mathrm{MIN}\ell\text{-}\mathrm{pKT}^O\in\mathsf{prBPP}$.
--
--   Easiness of the mild gap problem for $\mathrm{pK}$ carries over to the measure $\ell$-$\mathrm{pK}$, which is the form needed by Lemma 3.8.
--
--   Differences from the source:
--   - reading: instances (x, 1^s, 1^t, 1^a, 1^b) with any a, b in Defs. 2.9/2.10 → an instance is in YES or NO only if 1 ≤ b ≤ a; reason: b/a and (b−1)/a must lie in [0,1], the domain of Def. 2.2; read literally, (x, 1^0, 1^0, 1^1, 1^0) is in YES ∩ NO (pK^0_0(x) = 0 ≤ 0 and pK^{ρ(1)}_{−1}(x) = 0 ≥ 0 + log 1), so no oracle's problem would be in prBPP
--   - reading: instances of Def. 3.6 with any a, b, c, d → an instance is in YES or NO only if 2 ≤ b < a and 2 ≤ d < c; reason: the four parameters must lie in (0,1), the domain of Def. 3.5
--   - encoding: a constant c > 0 with ρ(n) = n^c → an integer c ≥ 1; reason: ρ is ℕ-valued; a larger c only shrinks NO, so integer c ≥ 1 is equivalent
--   - encoding: multi-tape machines over {0,1,⊥} with a fixed standard encoding (details unspecified) → the concrete Machine (alphabet {0,1,⊥,blank}, one-way infinite tapes, one-step oracle answers) and the concrete encoding code; reason: the paper fixes none of these details
--   - encoding: tuples and pairs of strings → the self-delimiting tupleEnc / pairStr; reason: the paper fixes no encoding
--   - encoding: minima over ℕ, log, comparisons with s + log ρ → values in ℕ∞ (⊤ for an empty minimum), Real.logb 2, comparisons in EReal; reason: Lean convention; same instances
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Lemma 3.7, p.22

import Mathlib
import Definitions.Def_AvgWorstGap_MildGapMINpKT
import Definitions.Def_AvgWorstGap_MildGapMINlpKT

namespace AvgWorstGap

open NKtLB

/-- **Lemma 3.7** (arXiv:2610.19162, version of October 30, 2026, p.22): "For every oracle `O`, if `Mild-Gap-MINpKT^O ∈ prBPP`, then
`Mild-Gap-MINℓ-pKT^O ∈ prBPP`." -/
theorem lemma_3_7_mild_gap_lpK (O : Set (List Bool)) (h : MildGapInPrBPP O) :
    MildGapLInPrBPP O := by sorry

end AvgWorstGap
