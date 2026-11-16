-- Prove2me | Theorems.Thm_AvgWorstGap_Supplement_theorem_4_3_np_eq_p_iff_mild_gap
-- name    : AvgWorstGap.Supplement.theorem_4_3_np_eq_p_iff_mild_gap
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:09:08.664225+00:00
-- url     : https://prove2.me/theorems/4981fdf2-b4a5-4416-8802-929910ac57e7
-- title:
--   Theorem 4.3 — $\mathsf{NP}=\mathsf{P}$ iff $\mathrm{Mild}\text{-}\mathrm{Gap}\text{-}\mathrm{MINKT}^{\mathsf{PH}}\in\mathsf P$ (corrected: $t\ge2$ in Mild-Gap-MINKT)
-- statement:
--   $$\mathsf{NP}=\mathsf{P}\iff\mathrm{Mild}\text{-}\mathrm{Gap}\text{-}\mathrm{MINKT}^{\mathsf{PH}}\in\mathsf P.$$
--
--   Here $\mathrm{Mild}\text{-}\mathrm{Gap}\text{-}\mathrm{MINKT}^{\mathsf{PH}}\in\mathsf P$ means that for every $L\in\mathsf{PH}$ there is a constant $c$ such that the promise problem $\mathrm{Mild}\text{-}\mathrm{Gap}_\rho\text{-}\mathrm{MINKT}^L$ with $\rho(n)=n^c$ — YES: $K^{t,L}(x)\le s$; NO: $K^{t+\rho(|x|),L}(x)\ge s+\log\rho(t)$ — is decidable in deterministic polynomial time.
--
--   The theorem characterizes the worst-case question $\mathsf{NP}=\mathsf{P}$ by the worst-case complexity of estimating $K^t$ within a mild time gap. Together with Hirahara's characterization of $\mathrm{DistPH}\subseteq\mathsf{AvgP}$ by the standard gap problem, it yields Theorem 4.1.
--
--   Differences from the source:
--   - correction: Gap_ρ-MINKT^O and Mild-Gap_ρ-MINKT^O (Defs. 2.6, 2.7) on instances (x, 1^s, 1^t) for every t → an instance is in YES or NO only if t ≥ 2; reason: printed, YES ∩ NO ≠ ∅ at t ≤ 1: with ρ(n) = n^c, log ρ(0) = 0, and K^{0,O}(ϵ) = k₀ < ∞ (a single machine halting at step 0), so (ϵ, 1^{k₀}, 1^0) is in YES and in NO for every oracle O and every c (proved in the sanity file); then no algorithm decides either problem and "∈ P" is false for every oracle, which makes Theorem 4.1 item 2 vacuous and Theorem 4.3 read NP ≠ P; for t ≥ 2, log ρ(t) ≥ 1 and YES, NO are disjoint
--   - encoding: a constant c > 0 with ρ(n) = n^c → an integer c ≥ 1; reason: ρ is ℕ-valued; a larger c only shrinks NO, so integer c ≥ 1 is equivalent
--   - encoding: P for languages; PH = P, NP = P → L ∈ P iff (L, Lᶜ) ∈ prP; class equality as ∀ L, L ∈ PH ↔ L ∈ P (resp. NP); reason: standard; both inclusions are stated
--   - encoding: multi-tape machines with a fixed standard encoding (details unspecified) → the published Machine and the published encoding code; reason: the paper fixes none of these details
--   - encoding: tuples (x, 1^s, 1^t, …) and (z; 1^k) → the self-delimiting tupleEnc; reason: the paper fixes no encoding
--   - encoding: minima over ℕ, log, comparisons with s + log ρ → values in ℕ∞ (⊤ for an empty minimum), Real.logb 2, comparisons in EReal; reason: Lean convention; same instances
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Theorem 4.3, p.34 (proof p.35)

import Mathlib
import Definitions.Def_AvgWorstGap_Supplement_GapMINKT

namespace AvgWorstGap.Supplement

open NKtLB

/-- **Theorem 4.3** (Goldberg, Hu, Lu, Lyu, Oliveira, *The Gap Between Average-Case and Worst-Case Complexity*,
arXiv:2610.19162, version of October 30, 2026, p.34): "The following holds: `NP = P ⇐⇒ Mild-Gap-MINKT^PH ∈ P`."

**Formalization Note.** `NP = P` is the equality of classes of languages (`NPEqP`). "`Mild-Gap-MINKT^PH
∈ P`" means: for every `L ∈ PH` there is an integer `c ≥ 1` with `Mild-Gap_ρ-MINKT^L`
(`ρ(n) = n^c`) in `prP` (p.15), with the guard `t ≥ 2` (correction, see `MildGapMINKT`). -/
theorem theorem_4_3_np_eq_p_iff_mild_gap : NPEqP ↔ MildGapKTPHInP := by sorry

end AvgWorstGap.Supplement
