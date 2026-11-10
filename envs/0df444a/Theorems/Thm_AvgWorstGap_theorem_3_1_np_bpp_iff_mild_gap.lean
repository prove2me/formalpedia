-- Prove2me | Theorems.Thm_AvgWorstGap_theorem_3_1_np_bpp_iff_mild_gap
-- name    : AvgWorstGap.theorem_3_1_np_bpp_iff_mild_gap
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:53:01.094901+00:00
-- url     : https://prove2.me/theorems/e0234bdc-6a37-4d53-998b-32c42db95fef
-- title:
--   Theorem 3.1 — NP ⊆ BPP iff Mild-Gap-MINpKT^PH ∈ prBPP
-- statement:
--   $$\mathsf{NP}\subseteq\mathsf{BPP}\iff\mathrm{Mild}\text{-}\mathrm{Gap}\text{-}\mathrm{MINpKT}^{\mathsf{PH}}\in\mathsf{prBPP}.$$
--
--   Worst-case easiness of NP is characterized by worst-case easiness of the mild gap version of estimating $\mathrm{pK}$ with a $\mathsf{PH}$ oracle. This is one of the two characterizations combined in Theorem 1.1.
--
--   Differences from the source:
--   - reading: instances (x, 1^s, 1^t, 1^a, 1^b) with any a, b in Defs. 2.9/2.10 → an instance is in YES or NO only if 1 ≤ b ≤ a; reason: b/a and (b−1)/a must lie in [0,1], the domain of Def. 2.2; read literally, (x, 1^0, 1^0, 1^1, 1^0) is in YES ∩ NO (pK^0_0(x) = 0 ≤ 0 and pK^{ρ(1)}_{−1}(x) = 0 ≥ 0 + log 1), so no oracle's problem would be in prBPP
--   - encoding: a constant c > 0 with ρ(n) = n^c → an integer c ≥ 1; reason: ρ is ℕ-valued; a larger c only shrinks NO, so integer c ≥ 1 is equivalent
--   - encoding: multi-tape machines over {0,1,⊥} with a fixed standard encoding (details unspecified) → the concrete Machine (alphabet {0,1,⊥,blank}, one-way infinite tapes, one-step oracle answers) and the concrete encoding code; reason: the paper fixes none of these details
--   - encoding: tuples and pairs of strings → the self-delimiting tupleEnc / pairStr; reason: the paper fixes no encoding
--   - encoding: minima over ℕ, log, comparisons with s + log ρ → values in ℕ∞ (⊤ for an empty minimum), Real.logb 2, comparisons in EReal; reason: Lean convention; same instances
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Theorem 3.1, p.19

import Mathlib
import Definitions.Def_AvgWorstGap_MildGapMINpKT
import Definitions.Def_AvgWorstGap_DistPHSubAvgBPP

namespace AvgWorstGap

open NKtLB

/-- **Theorem 3.1** (arXiv:2610.19162, version of October 30, 2026, p.19): "`NP ⊆ BPP ⇐⇒ Mild-Gap-MINpKT^PH ∈ prBPP`." -/
theorem theorem_3_1_np_bpp_iff_mild_gap : NPSubBPP ↔ MildGapPHInPrBPP := by sorry

end AvgWorstGap
