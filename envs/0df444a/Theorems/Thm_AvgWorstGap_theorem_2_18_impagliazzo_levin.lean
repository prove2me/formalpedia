-- Prove2me | Theorems.Thm_AvgWorstGap_theorem_2_18_impagliazzo_levin
-- name    : AvgWorstGap.theorem_2_18_impagliazzo_levin
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:48:36.051403+00:00
-- url     : https://prove2.me/theorems/6f1a80fd-bc96-43f7-bbfd-587dd81a5107
-- title:
--   Theorem 2.18 — uniform easiness of NP^A extends to all samplable distributions (cited from [IL90])
-- statement:
--   Let $A$ be any oracle. If $(L,U)\in\mathsf{AvgBPP}$ for every $L\in\mathsf{NP}^A$, where $U$ is the uniform family, then $(L,D)\in\mathsf{AvgBPP}$ for every $D\in\mathsf{PSAMP}$ and every $L\in\mathsf{NP}^A$.
--
--   Average-case easiness of $\mathsf{NP}^A$ under the uniform distribution implies its average-case easiness under every polynomial-time samplable distribution. This is the result of Impagliazzo and Levin [IL90], used in the proof of Lemma 3.13. The heuristic schemes and the samplers have no oracle, as printed.
--
--   Differences from the source:
--   - reading: AvgBPP conditions for every n, k ∈ ℕ → for every n and every k ≥ 1; reason: 1 − 1/k is undefined at k = 0
--   - reading: PSAMP samplers for every n ≥ 1, D_0 unconstrained → a sampler for every n ∈ ℕ (D_0 is the output distribution of A(1^0)); reason: AvgBPP quantifies every n ∈ ℕ, so an unconstrained D_0 of full support would force L ∈ BPP for every (L, D) ∈ AvgBPP and collapse DistPH ⊆ AvgBPP to PH ⊆ BPP
--   - encoding: multi-tape machines over {0,1,⊥} with a fixed standard encoding (details unspecified) → the concrete Machine (alphabet {0,1,⊥,blank}, one-way infinite tapes, one-step oracle answers) and the concrete encoding code; reason: the paper fixes none of these details
--   - encoding: distribution families and Pr_{x∼D_n} → PMF (List Bool) and its outer measure; reason: Lean convention; same distributions
--   - encoding: tuples and pairs of strings → the self-delimiting tupleEnc / pairStr; reason: the paper fixes no encoding
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Theorem 2.18, p.18

import Mathlib
import Definitions.Def_AvgWorstGap_DistPHSubAvgBPP

namespace AvgWorstGap

open NKtLB

/-- **Theorem 2.18 ([IL90])** (cited; arXiv:2610.19162, version of October 30, 2026, p.18): "Let `A` be any oracle. If
`(NP^A, U) ⊆ AvgBPP`, then for every distribution `D ∈ PSAMP` and `L ∈ NP^A`, we have
`(L, D) ∈ AvgBPP`."

**Formalization Note.** `U` is the uniform family; `AvgBPP` and `PSAMP` are unrelativized (the
heuristic scheme and the sampler have no oracle), as printed. -/
theorem theorem_2_18_impagliazzo_levin (A : Set (List Bool))
    (h : ∀ L : Set (List Bool), InNPO A L → AvgBPP L uniformFamily) :
    ∀ D : ℕ → PMF (List Bool), InPSAMP D → ∀ L : Set (List Bool), InNPO A L → AvgBPP L D := by sorry

end AvgWorstGap
