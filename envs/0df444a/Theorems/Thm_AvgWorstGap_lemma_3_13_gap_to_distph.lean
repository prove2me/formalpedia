-- Prove2me | Theorems.Thm_AvgWorstGap_lemma_3_13_gap_to_distph
-- name    : AvgWorstGap.lemma_3_13_gap_to_distph
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:51:02.672375+00:00
-- url     : https://prove2.me/theorems/c0989d23-1d13-496a-915e-02308bd2f566
-- title:
--   Lemma 3.13 — Gap-MINpKT^PH ∈ prBPP implies DistPH ⊆ AvgBPP
-- statement:
--   If $\mathrm{Gap}\text{-}\mathrm{MINpKT}^{\mathsf{PH}}\in\mathsf{prBPP}$, then $\mathrm{DistPH}\subseteq\mathsf{AvgBPP}$.
--
--   This is the backward direction of Theorem 3.2: worst-case easiness of the standard gap problem with $\mathsf{PH}$ oracles makes every $\mathsf{PH}$ language easy on average under every samplable distribution.
--
--   Differences from the source:
--   - reading: instances (x, 1^s, 1^t, 1^a, 1^b) with any a, b in Defs. 2.9/2.10 → an instance is in YES or NO only if 1 ≤ b ≤ a; reason: b/a and (b−1)/a must lie in [0,1], the domain of Def. 2.2; read literally, (x, 1^0, 1^0, 1^1, 1^0) is in YES ∩ NO (pK^0_0(x) = 0 ≤ 0 and pK^{ρ(1)}_{−1}(x) = 0 ≥ 0 + log 1), so no oracle's problem would be in prBPP
--   - encoding: a constant c > 0 with ρ(n) = n^c → an integer c ≥ 1; reason: ρ is ℕ-valued; a larger c only shrinks NO, so integer c ≥ 1 is equivalent
--   - reading: AvgBPP conditions for every n, k ∈ ℕ → for every n and every k ≥ 1; reason: 1 − 1/k is undefined at k = 0
--   - reading: PSAMP samplers for every n ≥ 1, D_0 unconstrained → a sampler for every n ∈ ℕ (D_0 is the output distribution of A(1^0)); reason: AvgBPP quantifies every n ∈ ℕ, so an unconstrained D_0 of full support would force L ∈ BPP for every (L, D) ∈ AvgBPP and collapse DistPH ⊆ AvgBPP to PH ⊆ BPP
--   - encoding: multi-tape machines over {0,1,⊥} with a fixed standard encoding (details unspecified) → the concrete Machine (alphabet {0,1,⊥,blank}, one-way infinite tapes, one-step oracle answers) and the concrete encoding code; reason: the paper fixes none of these details
--   - encoding: tuples and pairs of strings → the self-delimiting tupleEnc / pairStr; reason: the paper fixes no encoding
--   - encoding: minima over ℕ, log, comparisons with s + log ρ → values in ℕ∞ (⊤ for an empty minimum), Real.logb 2, comparisons in EReal; reason: Lean convention; same instances
--   - encoding: distribution families and Pr_{x∼D_n} → PMF (List Bool) and its outer measure; reason: Lean convention; same distributions
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Lemma 3.13, p.27

import Mathlib
import Definitions.Def_AvgWorstGap_GapMINpKT
import Definitions.Def_AvgWorstGap_DistPHSubAvgBPP

namespace AvgWorstGap

open NKtLB

/-- **Lemma 3.13** (arXiv:2610.19162, version of October 30, 2026, p.27): "If `Gap-MINpKT^PH ∈ prBPP`, then `DistPH ⊆ AvgBPP`." -/
theorem lemma_3_13_gap_to_distph (h : GapPHInPrBPP) : DistPHSubAvgBPP := by sorry

end AvgWorstGap
