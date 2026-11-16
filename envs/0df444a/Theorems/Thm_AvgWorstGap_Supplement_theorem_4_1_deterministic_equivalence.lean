-- Prove2me | Theorems.Thm_AvgWorstGap_Supplement_theorem_4_1_deterministic_equivalence
-- name    : AvgWorstGap.Supplement.theorem_4_1_deterministic_equivalence
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:08:24.958778+00:00
-- url     : https://prove2.me/theorems/e786796c-993b-478b-a871-83d376676f57
-- title:
--   Theorem 4.1 — the deterministic equivalence: excluding PH-Heuristica iff the gap reduction for $K^{\mathsf{PH}}$ (corrected: $t\ge2$ in Gap/Mild-Gap-MINKT)
-- statement:
--   The following two statements are equivalent.
--
--   1. **(Exclusion of PH-Heuristica)** If $\mathrm{DistPH}\subseteq\mathsf{AvgP}$, then $\mathsf{PH}=\mathsf{P}$.
--   2. **(Meta-complexity of $K^{\mathsf{PH}}$)** If $\mathrm{Gap}\text{-}\mathrm{MINKT}^{\mathsf{PH}}\in\mathsf P$, then $\mathrm{Mild}\text{-}\mathrm{Gap}\text{-}\mathrm{MINKT}^{\mathsf{PH}}\in\mathsf P$.
--
--   $$\big(\mathrm{DistPH}\subseteq\mathsf{AvgP}\Rightarrow\mathsf{PH}=\mathsf{P}\big)\iff\big(\mathrm{Gap}\text{-}\mathrm{MINKT}^{\mathsf{PH}}\in\mathsf P\Rightarrow\mathrm{Mild}\text{-}\mathrm{Gap}\text{-}\mathrm{MINKT}^{\mathsf{PH}}\in\mathsf P\big).$$
--
--   Here $\mathsf{AvgP}$ is the class of distributional problems with a deterministic errorless heuristic scheme, $\mathrm{DistPH}$ pairs every $L\in\mathsf{PH}$ with every polynomial-time samplable distribution family, and "$A^{\mathsf{PH}}\in\mathsf P$" means that for every $L\in\mathsf{PH}$ there is a constant $c$ such that $A^L$, with gap parameter $\rho(n)=n^c$, is decidable in deterministic polynomial time on its promise.
--
--   This is the deterministic analogue of the main equivalence (Theorem 1.1): with time-bounded Kolmogorov complexity $K^t$ in place of $\mathrm{pK}^t$, it reduces the exclusion of deterministic PH-Heuristica to a worst-case question about two approximation regimes of $K^t$.
--
--   Differences from the source:
--   - correction: Gap_ρ-MINKT^O and Mild-Gap_ρ-MINKT^O (Defs. 2.6, 2.7) on instances (x, 1^s, 1^t) for every t → an instance is in YES or NO only if t ≥ 2; reason: printed, YES ∩ NO ≠ ∅ at t ≤ 1: with ρ(n) = n^c, log ρ(0) = 0, and K^{0,O}(ϵ) = k₀ < ∞ (a single machine halting at step 0), so (ϵ, 1^{k₀}, 1^0) is in YES and in NO for every oracle O and every c (proved in the sanity file); then no algorithm decides either problem and "∈ P" is false for every oracle, which makes Theorem 4.1 item 2 vacuous and Theorem 4.3 read NP ≠ P; for t ≥ 2, log ρ(t) ≥ 1 and YES, NO are disjoint
--   - reading: heuristic-scheme conditions for every n, k ∈ ℕ → for every n and every k ≥ 1; reason: 1 − 1/k is undefined at k = 0
--   - reading: PSAMP samplers for every n ≥ 1, D_0 unconstrained → a sampler for every n ∈ ℕ (the published InPSAMP); reason: the schemes quantify every n ∈ ℕ, so an unconstrained D_0 of full support would force L to be decidable in the worst case for every (L, D) in the average-case class
--   - encoding: a constant c > 0 with ρ(n) = n^c → an integer c ≥ 1; reason: ρ is ℕ-valued; a larger c only shrinks NO, so integer c ≥ 1 is equivalent
--   - encoding: P for languages; PH = P, NP = P → L ∈ P iff (L, Lᶜ) ∈ prP; class equality as ∀ L, L ∈ PH ↔ L ∈ P (resp. NP); reason: standard; both inclusions are stated
--   - encoding: multi-tape machines with a fixed standard encoding (details unspecified) → the published Machine and the published encoding code; reason: the paper fixes none of these details
--   - encoding: tuples (x, 1^s, 1^t, …) and (z; 1^k) → the self-delimiting tupleEnc; reason: the paper fixes no encoding
--   - encoding: minima over ℕ, log, comparisons with s + log ρ → values in ℕ∞ (⊤ for an empty minimum), Real.logb 2, comparisons in EReal; reason: Lean convention; same instances
--   - encoding: distribution families and Pr_{x∼D_n} → PMF (List Bool) and its outer measure; reason: Lean convention; same distributions
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Theorem 4.1, p.34

import Mathlib
import Definitions.Def_AvgWorstGap_Supplement_AvgP
import Definitions.Def_AvgWorstGap_Supplement_GapMINKT

namespace AvgWorstGap.Supplement

open NKtLB

/-- **Theorem 4.1** (Goldberg, Hu, Lu, Lyu, Oliveira, *The Gap Between Average-Case and Worst-Case Complexity*,
arXiv:2610.19162, version of October 30, 2026, p.34): "The following statements are equivalent:
1. (Exclusion of PH-Heuristica). `DistPH ⊆ AvgP =⇒ PH = P`.
2. (Meta-Complexity of K^PH). `Gap-MINKT^PH ∈ P =⇒ Mild-Gap-MINKT^PH ∈ P`."

**Formalization Note.** "`A^PH ∈ P`" means: for every `L ∈ PH` there is an integer `c ≥ 1` with
`A^L` (gap `ρ(n) = n^c`) in `prP` (p.15). Both promise problems carry the guard `t ≥ 2`
(correction: at `t ≤ 1` the printed YES and NO intersect, see `GapMINKT`). PSAMP is the published
`InPSAMP` (a sampler for every `n ∈ ℕ`). -/
theorem theorem_4_1_deterministic_equivalence :
    (DistPHSubAvgP → PHEqP) ↔ (GapKTPHInP → MildGapKTPHInP) := by sorry

end AvgWorstGap.Supplement
