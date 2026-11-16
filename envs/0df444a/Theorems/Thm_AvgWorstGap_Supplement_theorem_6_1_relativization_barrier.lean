-- Prove2me | Theorems.Thm_AvgWorstGap_Supplement_theorem_6_1_relativization_barrier
-- name    : AvgWorstGap.Supplement.theorem_6_1_relativization_barrier
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:12:23.816161+00:00
-- url     : https://prove2.me/theorems/51dca30a-c3dd-41df-8e70-0d9e8d8e2e8f
-- title:
--   Theorem 6.1 — an oracle world where $\mathrm{Gap}\text{-}\mathrm{MINpKT}^{\mathsf{PH}}$ is easy while $\mathrm{Mild}\text{-}\mathrm{Gap}\text{-}\mathrm{MINpKT}^{\mathsf{PH}}$ is hard
-- statement:
--   There is an oracle $O\subseteq\{0,1\}^*$ such that
--
--   $$\mathrm{Gap}\text{-}\mathrm{MINpKT}^{\mathsf{PH}^O,O}\in\mathsf{prBPP}^O\quad\text{but}\quad\mathrm{Mild}\text{-}\mathrm{Gap}\text{-}\mathrm{MINpKT}^{\mathsf{PH}^O,O}\notin\mathsf{prBPP}^O.$$
--
--   Explicitly, the same oracle $O$ satisfies both:
--
--   1. for every $L\in\mathsf{PH}^O$ there are a polynomial $\rho$ and a probabilistic polynomial-time machine with oracle $O$ that decides $\mathrm{Gap}_\rho\text{-}\mathrm{MINpKT}^{L,O}$ (YES: $\mathrm{pK}^{t,L,O}_{b/a}(x)\le s$; NO: $\mathrm{pK}^{\rho(t+a+b),L,O}_{(b-1)/a}(x)\ge s+\log\rho(t+a+b)$);
--   2. there is $L\in\mathsf{PH}^O$ such that for no constant $c\ge1$ is $\mathrm{Mild}\text{-}\mathrm{Gap}_\rho\text{-}\mathrm{MINpKT}^{L,O}$, with $\rho(n)=c\cdot n^c$ (NO: $\mathrm{pK}^{t+\rho(|x|+a+b),L,O}_{(b-1)/a}(x)\ge s+\log\rho(t+a+b)$), in $\mathsf{prBPP}^O$.
--
--   Here $\mathrm{pK}^{t,L,O}_\lambda$ is probabilistic time-bounded Kolmogorov complexity for programs with oracle access to both $L$ and $O$.
--
--   The theorem is a relativization barrier: any proof that the gap reduction of Theorem 1.1 holds ("$\mathrm{Gap}\text{-}\mathrm{MINpKT}^{\mathsf{PH}}\in\mathsf{prBPP}$ implies $\mathrm{Mild}\text{-}\mathrm{Gap}\text{-}\mathrm{MINpKT}^{\mathsf{PH}}\in\mathsf{prBPP}$") must use non-relativizing techniques.
--
--   Differences from the source:
--   - reading: K^{t,L,O}(x | r) inside pK^{t,L,O}_λ → Def. 2.2's K^{t}(x | ϵ; r) with oracle L ⊕ O, r ∈ {0,1}^t on the randomness tape; reason: §6 obtains relativization "by providing oracle access to all machines involved", i.e. from Def. 2.2
--   - encoding: programs with oracle access to both L and O → programs with oracle L ⊕ O = {0u : u ∈ L} ∪ {1u : u ∈ O}; reason: standard join; one extra bit per query
--   - reading: instances (x, 1^s, 1^t, 1^a, 1^b) with any a, b → an instance is in YES or NO only if 1 ≤ b ≤ a; reason: b/a and (b − 1)/a must lie in [0, 1], the domain of Def. 2.2 (the guard of the published Gap/Mild-Gap-MINpKT)
--   - encoding: a polynomial ρ → ρ ∈ Polynomial ℕ, evaluated at n; reason: NO shrinks as ρ grows and every polynomial ℕ → ℕ is dominated by one with natural coefficients, so the existential is the same
--   - encoding: a constant c ≥ 1 with ρ(n) = c·n^c → an integer c ≥ 1; reason: ρ is ℕ-valued; NO shrinks as c grows, so excluding every integer c ≥ 1 excludes every real c ≥ 1
--   - encoding: multi-tape machines with a fixed standard encoding (details unspecified) → the published Machine and the published encoding code; reason: the paper fixes none of these details
--   - encoding: tuples (x, 1^s, 1^t, …) and (z; 1^k) → the self-delimiting tupleEnc; reason: the paper fixes no encoding
--   - encoding: minima over ℕ, log, comparisons with s + log ρ → values in ℕ∞ (⊤ for an empty minimum), Real.logb 2, comparisons in EReal; reason: Lean convention; same instances
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), §6, Theorem 6.1, p.39 (definitions pp.38–39; proof sketch pp.39–40)

import Mathlib
import Definitions.Def_AvgWorstGap_Supplement_Relativized

namespace AvgWorstGap.Supplement

open NKtLB

/-- **Theorem 6.1 (Oracle world where Gap-MINpKT^PH is easy while Mild-Gap-MINpKT^PH is hard)**
(Goldberg, Hu, Lu, Lyu, Oliveira, *The Gap Between Average-Case and Worst-Case Complexity*,
arXiv:2610.19162, version of October 30, 2026, p.39): "There is an oracle `O` such that `Gap-MINpKT^{PH^O,O} ∈ prBPP^O` but
`Mild-Gap-MINpKT^{PH^O,O} ∉ prBPP^O`."

**Formalization Note.** Both halves are the explicit definitions of pp.38–39 (`GapPHOInPrBPPO`,
`MildGapPHONotInPrBPPO`); the `∉` half is "some `L ∈ PH^O` such that for no `c ≥ 1`,
`Mild-Gap_{c·n^c}-MINpKT^{L,O} ∈ prBPP^O`", not the negation of the `∈` half. Programs inside
`pK` query the join `L ⊕ O`; the deciders query `O`. -/
theorem theorem_6_1_relativization_barrier :
    ∃ O : Set (List Bool), GapPHOInPrBPPO O ∧ MildGapPHONotInPrBPPO O := by sorry

end AvgWorstGap.Supplement
