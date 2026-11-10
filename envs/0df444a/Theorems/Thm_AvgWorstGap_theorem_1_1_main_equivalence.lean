-- Prove2me | Theorems.Thm_AvgWorstGap_theorem_1_1_main_equivalence
-- name    : AvgWorstGap.theorem_1_1_main_equivalence
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:52:31.921174+00:00
-- url     : https://prove2.me/theorems/ccfb6dd8-d489-4c75-9862-3522f6a3f461
-- title:
--   Theorem 1.1 — excluding PH Heuristica is equivalent to the gap reduction for pK^PH
-- statement:
--   The following two statements are equivalent.
--
--   1. **(Exclusion of PH Heuristica)** If $\mathrm{DistPH}\subseteq\mathsf{AvgBPP}$, then $\mathsf{PH}\subseteq\mathsf{BPP}$.
--   2. **(Gap reduction for $\mathrm{pK}^{\mathsf{PH}}$)** If $\mathrm{Gap}\text{-}\mathrm{MINpKT}^{\mathsf{PH}}\in\mathsf{prBPP}$, then $\mathrm{Mild}\text{-}\mathrm{Gap}\text{-}\mathrm{MINpKT}^{\mathsf{PH}}\in\mathsf{prBPP}$.
--
--   $$\big(\mathrm{DistPH}\subseteq\mathsf{AvgBPP}\Rightarrow\mathsf{PH}\subseteq\mathsf{BPP}\big)\iff\big(\mathrm{Gap}\text{-}\mathrm{MINpKT}^{\mathsf{PH}}\in\mathsf{prBPP}\Rightarrow\mathrm{Mild}\text{-}\mathrm{Gap}\text{-}\mathrm{MINpKT}^{\mathsf{PH}}\in\mathsf{prBPP}\big).$$
--
--   Here "$A^{\mathsf{PH}}\in\mathsf{prBPP}$" means that for every oracle language $L\in\mathsf{PH}$ there is a constant $c$ with the problem $A^L$, with gap parameter $\rho(n)=n^c$, in $\mathsf{prBPP}$.
--
--   The theorem turns the open question of whether average-case easiness of $\mathsf{PH}$ implies worst-case easiness into a question about two approximation regimes of a single meta-computational problem, both in the worst case. The standard gap (time $\mathrm{poly}(t)$ on the NO side) captures average-case complexity, and the mild gap (time $t+\mathrm{poly}(n)$) captures worst-case complexity.
--
--   Differences from the source:
--   - reading: instances (x, 1^s, 1^t, 1^a, 1^b) with any a, b in Defs. 2.9/2.10 → an instance is in YES or NO only if 1 ≤ b ≤ a; reason: b/a and (b−1)/a must lie in [0,1], the domain of Def. 2.2; read literally, (x, 1^0, 1^0, 1^1, 1^0) is in YES ∩ NO (pK^0_0(x) = 0 ≤ 0 and pK^{ρ(1)}_{−1}(x) = 0 ≥ 0 + log 1), so no oracle's problem would be in prBPP
--   - reading: AvgBPP conditions for every n, k ∈ ℕ → for every n and every k ≥ 1; reason: 1 − 1/k is undefined at k = 0
--   - reading: PSAMP samplers for every n ≥ 1, D_0 unconstrained → a sampler for every n ∈ ℕ (D_0 is the output distribution of A(1^0)); reason: AvgBPP quantifies every n ∈ ℕ, so an unconstrained D_0 of full support would force L ∈ BPP for every (L, D) ∈ AvgBPP and collapse DistPH ⊆ AvgBPP to PH ⊆ BPP
--   - encoding: a constant c > 0 with ρ(n) = n^c → an integer c ≥ 1; reason: ρ is ℕ-valued; a larger c only shrinks NO, so integer c ≥ 1 is equivalent
--   - encoding: multi-tape machines over {0,1,⊥} with a fixed standard encoding (details unspecified) → the concrete Machine (alphabet {0,1,⊥,blank}, one-way infinite tapes, one-step oracle answers) and the concrete encoding code; reason: the paper fixes none of these details
--   - encoding: tuples and pairs of strings → the self-delimiting tupleEnc / pairStr; reason: the paper fixes no encoding
--   - encoding: minima over ℕ, log, comparisons with s + log ρ → values in ℕ∞ (⊤ for an empty minimum), Real.logb 2, comparisons in EReal; reason: Lean convention; same instances
--   - encoding: distribution families and Pr_{x∼D_n} → PMF (List Bool) and its outer measure; reason: Lean convention; same distributions
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Theorem 1.1, p.4 (restated p.19)

import Mathlib
import Definitions.Def_AvgWorstGap_GapMINpKT
import Definitions.Def_AvgWorstGap_MildGapMINpKT
import Definitions.Def_AvgWorstGap_DistPHSubAvgBPP

namespace AvgWorstGap

open NKtLB

/-- **Theorem 1.1 (Main Equivalence)** (Goldberg, Hu, Lu, Lyu, Oliveira, *The Gap Between
Average-Case and Worst-Case Complexity*, arXiv:2610.19162, version of October 30, 2026, p.4, restated p.19): "The following
statements are equivalent: 1. (Exclusion of PH Heuristica). `DistPH ⊆ AvgBPP =⇒ PH ⊆ BPP`.
2. (Gap Reduction for pK^PH). `Gap-MINpKT^PH ∈ prBPP =⇒ Mild-Gap-MINpKT^PH ∈ prBPP`."

**Formalization Note.** "`A^PH ∈ prBPP`" means: for every `L ∈ PH` there is an integer `c ≥ 1`
with `A^L` (gap `ρ(n) = n^c`) in `prBPP` (pp.4, 15). Both promise problems carry the guard
`1 ≤ b ≤ a` (the domain of Def. 2.2). -/
theorem theorem_1_1_main_equivalence :
    (DistPHSubAvgBPP → PHSubBPP) ↔ (GapPHInPrBPP → MildGapPHInPrBPP) := by sorry

end AvgWorstGap
