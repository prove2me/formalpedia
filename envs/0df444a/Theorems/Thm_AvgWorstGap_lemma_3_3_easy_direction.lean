-- Prove2me | Theorems.Thm_AvgWorstGap_lemma_3_3_easy_direction
-- name    : AvgWorstGap.lemma_3_3_easy_direction
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:52:45.134201+00:00
-- url     : https://prove2.me/theorems/a3917c1e-c79b-44d0-83c0-e79ab2177144
-- title:
--   Lemma 3.3 — NP ⊆ BPP implies Mild-Gap-MINpKT^PH ∈ prBPP
-- statement:
--   If $\mathsf{NP}\subseteq\mathsf{BPP}$, then $\mathrm{Mild}\text{-}\mathrm{Gap}\text{-}\mathrm{MINpKT}^{\mathsf{PH}}\in\mathsf{prBPP}$: for every oracle $L\in\mathsf{PH}$ there is an integer $c\ge1$ such that $\mathrm{Mild}\text{-}\mathrm{Gap}_\rho\text{-}\mathrm{MINpKT}^L\in\mathsf{prBPP}$ with $\rho(n)=n^c$.
--
--   This is the easy direction of Theorem 3.1.
--
--   Differences from the source:
--   - reading: instances (x, 1^s, 1^t, 1^a, 1^b) with any a, b in Defs. 2.9/2.10 → an instance is in YES or NO only if 1 ≤ b ≤ a; reason: b/a and (b−1)/a must lie in [0,1], the domain of Def. 2.2; read literally, (x, 1^0, 1^0, 1^1, 1^0) is in YES ∩ NO (pK^0_0(x) = 0 ≤ 0 and pK^{ρ(1)}_{−1}(x) = 0 ≥ 0 + log 1), so no oracle's problem would be in prBPP
--   - encoding: a constant c > 0 with ρ(n) = n^c → an integer c ≥ 1; reason: ρ is ℕ-valued; a larger c only shrinks NO, so integer c ≥ 1 is equivalent
--   - encoding: multi-tape machines over {0,1,⊥} with a fixed standard encoding (details unspecified) → the concrete Machine (alphabet {0,1,⊥,blank}, one-way infinite tapes, one-step oracle answers) and the concrete encoding code; reason: the paper fixes none of these details
--   - encoding: tuples and pairs of strings → the self-delimiting tupleEnc / pairStr; reason: the paper fixes no encoding
--   - encoding: minima over ℕ, log, comparisons with s + log ρ → values in ℕ∞ (⊤ for an empty minimum), Real.logb 2, comparisons in EReal; reason: Lean convention; same instances
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Lemma 3.3, p.20

import Mathlib
import Definitions.Def_AvgWorstGap_MildGapMINpKT
import Definitions.Def_AvgWorstGap_DistPHSubAvgBPP

namespace AvgWorstGap

open NKtLB

/-- **Lemma 3.3** (arXiv:2610.19162, version of October 30, 2026, p.20): "If `NP ⊆ BPP`, then `Mild-Gap-MINpKT^PH ∈ prBPP`." -/
theorem lemma_3_3_easy_direction (h : NPSubBPP) : MildGapPHInPrBPP := by sorry

end AvgWorstGap
