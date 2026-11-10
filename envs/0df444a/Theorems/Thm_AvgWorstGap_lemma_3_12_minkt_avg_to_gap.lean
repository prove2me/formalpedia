-- Prove2me | Theorems.Thm_AvgWorstGap_lemma_3_12_minkt_avg_to_gap
-- name    : AvgWorstGap.lemma_3_12_minkt_avg_to_gap
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:51:40.274073+00:00
-- url     : https://prove2.me/theorems/cf58268b-d5ce-4462-90c1-f1c7a6cea74e
-- title:
--   Lemma 3.12 — average-case easiness of MINKT^O gives Gap-MINpKT^O ∈ prBPP
-- statement:
--   For every oracle $O$: if $(\mathrm{MINKT}^O,\mathsf{PSAMP})\subseteq\mathsf{AvgBPP}$, that is, $(\mathrm{MINKT}^O,D)\in\mathsf{AvgBPP}$ for every $D\in\mathsf{PSAMP}$, then $\mathrm{Gap}\text{-}\mathrm{MINpKT}^O\in\mathsf{prBPP}$.
--
--   This is a worst-case to average-case reduction for the gap problem. With $\mathrm{MINKT}^O\in\mathsf{PH}$ for $O\in\mathsf{PH}$, it gives the forward direction of Theorem 3.2 (Lemma 3.11).
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
--   - encoding: the promise language MINKT^O as the first component of (L, D) → the set of YES instances (non-instances not in L); reason: YES ∪ NO covers every instance; non-instances have no membership in the paper
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Lemma 3.12, p.27

import Mathlib
import Definitions.Def_AvgWorstGap_MINKT
import Definitions.Def_AvgWorstGap_GapMINpKT
import Definitions.Def_AvgWorstGap_DistPHSubAvgBPP

namespace AvgWorstGap

open NKtLB

/-- **Lemma 3.12** (arXiv:2610.19162, version of October 30, 2026, p.27): "For every oracle `O`, if `(MINKT^O, PSAMP) ⊆ AvgBPP`, then
`Gap-MINpKT^O ∈ prBPP`."

**Formalization Note.** `(MINKT^O, PSAMP) ⊆ AvgBPP`: for every `D ∈ PSAMP`, `(MINKT^O, D)` admits a
randomized errorless heuristic scheme (the scheme has no oracle). -/
theorem lemma_3_12_minkt_avg_to_gap (O : Set (List Bool))
    (h : ∀ D : ℕ → PMF (List Bool), InPSAMP D → AvgBPP (MINKT O) D) : GapInPrBPP O := by sorry

end AvgWorstGap
