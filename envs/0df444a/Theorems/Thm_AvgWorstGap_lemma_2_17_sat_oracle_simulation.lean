-- Prove2me | Theorems.Thm_AvgWorstGap_lemma_2_17_sat_oracle_simulation
-- name    : AvgWorstGap.lemma_2_17_sat_oracle_simulation
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:50:12.837029+00:00
-- url     : https://prove2.me/theorems/8eba511c-66bf-4077-81b9-c16917a83197
-- title:
--   Lemma 2.17 — simulating pnK with an NP^O-hard oracle
-- statement:
--   Let $O$ be an oracle and $L$ a language that is hard for $\mathsf{NP}^O$ under deterministic polynomial-time reductions. There is a constant $c$ such that for all strings $x,y$ and all $t\in\mathbb N$,
--   $$\mathrm{pK}^{t^c,L}(x\mid y)\le\mathrm{pnK}^{t,O}(x\mid y)+c\cdot\log t.$$
--   Both sides have $\lambda=2/3$.
--
--   With an $\mathsf{NP}^O$-hard oracle, a nondeterministic description can be made deterministic at a polynomial cost in time and a logarithmic cost in length. Together with Theorem 2.13 this gives language compression for $\mathrm{pK}^{t,\mathrm{SAT}}$.
--
--   Differences from the source:
--   - encoding: a constant c > 0 → an integer c ≥ 1; reason: t^c and the claim only become weaker for larger c, so integer c is equivalent
--   - encoding: multi-tape machines over {0,1,⊥} with a fixed standard encoding (details unspecified) → the concrete Machine (alphabet {0,1,⊥,blank}, one-way infinite tapes, one-step oracle answers) and the concrete encoding code; reason: the paper fixes none of these details
--   - reading: programs Π for nK^t and pnK^t → single machine-advice pairs (M, α) run with the guess tape; reason: the composition model of p.13 has no guess tape; the nondeterministic output is defined for the pair model of p.12
--   - encoding: minima over ℕ, log, comparisons with s + log ρ → values in ℕ∞ (⊤ for an empty minimum), Real.logb 2, comparisons in EReal; reason: Lean convention; same instances
--   - generalization: L hard for NP^O under deterministic polynomial-time reductions (kind unspecified) → L hard under deterministic polynomial-time Turing reductions (NP^O ⊆ P^L); reason: many-one hardness implies Turing hardness, so the statement specializes to the many-one reading; the proof (simulating the reduction from L0 to L, p.17) works for either
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Lemma 2.17, p.17

import Mathlib
import Definitions.Def_AvgWorstGap_pK
import Definitions.Def_AvgWorstGap_pnK
import Definitions.Def_AvgWorstGap_IsSigmaPComplete

namespace AvgWorstGap

open NKtLB

/-- **Lemma 2.17** (arXiv:2610.19162, version of October 30, 2026, p.17): "For every oracle `O` and every language `L` that is hard for
`NP^O` under deterministic polynomial-time reductions, there exists a constant `c > 0` such that,
for all `x, y ∈ {0, 1}∗` and `t ∈ ℕ`, `pK^{t^c,L}(x | y) ≤ pnK^{t,O}(x | y) + c · log t`."

**Formalization Note.** `λ = 2/3` on both sides (omitted in the paper). The left side is in the
composition model, the right side in single-pair programs. `c` is an integer `≥ 1`. `log` is
`Real.logb 2` (so `c · log t = 0` at `t ≤ 1`); comparison in `EReal`. "Hard under deterministic
polynomial-time reductions" is `IsNPOHard`, hardness under Turing reductions (`NP^O ⊆ P^L`), which
many-one hardness implies. -/
theorem lemma_2_17_sat_oracle_simulation (O L : Set (List Bool)) (hL : IsNPOHard O L) :
    ∃ c : ℕ, 1 ≤ c ∧ ∀ (x y : List Bool) (t : ℕ),
      toEReal (pK L (t ^ c) (2 / 3) x y) ≤
        toEReal (pnK O t (2 / 3) x y) + (((c : ℝ) * Real.logb 2 (t : ℝ) : ℝ) : EReal) := by sorry

end AvgWorstGap
