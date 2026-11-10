-- Prove2me | Theorems.Thm_AvgWorstGap_theorem_3_2_distph_iff_gap
-- name    : AvgWorstGap.theorem_3_2_distph_iff_gap
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:51:50.869984+00:00
-- url     : https://prove2.me/theorems/7413ea2f-b13a-4537-8694-c6106fdaca4e
-- title:
--   Theorem 3.2 — DistPH ⊆ AvgBPP iff Gap-MINpKT^PH ∈ prBPP
-- statement:
--   $$\mathrm{DistPH}\subseteq\mathsf{AvgBPP}\iff\mathrm{Gap}\text{-}\mathrm{MINpKT}^{\mathsf{PH}}\in\mathsf{prBPP}.$$
--
--   Average-case easiness of $\mathsf{PH}$ is characterized by worst-case easiness of the standard gap version of estimating $\mathrm{pK}$ with a $\mathsf{PH}$ oracle. This is the second characterization combined in Theorem 1.1. Its forward direction is Lemma 3.11, which follows from Lemma 3.12, and its backward direction is Lemma 3.13.
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
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Theorem 3.2, p.19

import Mathlib
import Definitions.Def_AvgWorstGap_GapMINpKT
import Definitions.Def_AvgWorstGap_DistPHSubAvgBPP

namespace AvgWorstGap

open NKtLB

/-- **Theorem 3.2** (arXiv:2610.19162, version of October 30, 2026, p.19): "`DistPH ⊆ AvgBPP ⇐⇒ Gap-MINpKT^PH ∈ prBPP`." -/
theorem theorem_3_2_distph_iff_gap : DistPHSubAvgBPP ↔ GapPHInPrBPP := by sorry

end AvgWorstGap
