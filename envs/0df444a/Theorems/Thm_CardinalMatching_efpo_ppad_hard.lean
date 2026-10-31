-- Prove2me | Theorems.Thm_CardinalMatching_efpo_ppad_hard
-- name    : CardinalMatching.efpo_ppad_hard
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:29:20.751993+00:00
-- url     : https://prove2.me/theorems/74fa59c1-3a5f-4266-9230-982df17301c3
-- title:
--   Theorem 8: finding an envy-free and Pareto-optimal allocation is PPAD-hard
-- statement:
--   Every search problem that reduces in polynomial time to APPROX-HZ$_c$ for every $c>0$ also reduces in polynomial time to EF+PO:
--   $$
--   \Big(\forall c>0:\ Q\le_p \text{APPROX-HZ}_c\Big)\ \Longrightarrow\ Q\le_p \text{EF+PO}\qquad\text{for every search problem } Q .
--   $$
--   Here EF+PO asks, for $n\ge 1$ and non-negative rational utilities $u\in\mathbb Q^{n\times n}$, for a rational fractional perfect matching that is envy-free and Pareto-optimal over all fractional perfect matchings. APPROX-HZ$_c$ asks, for rational utilities in $[0,1]$, for an $n^{-c}$-approximate Hylland–Zeckhauser equilibrium. Reductions are polynomial-time search reductions, correct for every answer.
--
--   By Theorem 9 (Chen et al. 2022), every problem in PPAD reduces to APPROX-HZ$_c$ for every $c>0$. Hence EF+PO is PPAD-hard: dropping prices from the Hylland–Zeckhauser scheme does not make envy-free and Pareto-optimal lotteries easier to compute.
--
--   **Formalization Note** No PPAD class is formalized; the statement is the reduction closure that yields Theorem 8 for any definition of PPAD-hardness by reductions from PPAD. The machine model is the public `CookPvsNP` Turing machine.
--
--   Differences from the source:
--   - generalization: "EF+PO is PPAD-hard" → every search problem that reduces to APPROX-HZ_c for all c > 0 reduces to EF+PO; reason: by Theorem 9 every PPAD problem satisfies the hypothesis, so this gives Theorem 8 for any definition of PPAD-hardness by reductions from PPAD, with no formal PPAD class
--   - reading: Theorem 9 (Chen et al. 2022), cited and not proved → enters only through the hypothesis ∀ c > 0, Q ≤ₚ APPROX-HZ_c with ε = n^(−c); reason: the paper's conclusion rests on this citation, which Lean does not have
--   - encoding: rational utilities, allocations and prices; "PPAD-hard" reductions unspecified → binary-encoded strings on Cook's Turing machines; polynomial-time search reductions correct for every answer; reason: the standard meaning of PPAD reductions, with rational data as on p.2
--   - reading: max { u_i · y | Σ_j y_j = 1, p · y ≤ 1 } in Definition 10 (the set can be empty) → IsApproxHZ asserts that this maximum exists (at least one bundle is feasible) and compares with it; reason: max ∅ is undefined; without this clause p_j = 1/(1 − ε), x_ij = (1 − ε)/n would be an answer on every instance
-- source:
--   Tröbst, Vazirani, Cardinal-Utility Matching Markets, arXiv:2402.08851v6, Theorem 8, p.6 (proof p.14); Theorem 9 (Chen et al. 2022), p.6

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_SearchReduces
import Definitions.Def_CardinalMatching_EFPO
import Definitions.Def_CardinalMatching_ApproxHZProblem

namespace CardinalMatching

/-- **Theorem 8** (Tröbst–Vazirani, *Cardinal-Utility Matching Markets*, arXiv:2402.08851v6, p.6): "The problem of finding an EF+PO allocation in a one-sided
matching market with linear utilities is PPAD-hard."

Stated as a reduction closure: every search problem `Q` that reduces in polynomial time to
APPROX-HZ_c (finding an `n^(−c)`-approximate HZ equilibrium, utilities in `[0, 1]`) for every
`c > 0` also reduces in polynomial time to EF+PO (non-negative rational utilities; answers are
envy-free and Pareto-optimal over all fractional perfect matchings).

**Formalization Note** Theorem 9 (Chen et al. 2022, cited on p.6: "For any c > 0, the problem of
finding an ǫ-approximate HZ equilibrium is PPAD-hard for ǫ ≤ 1/n^c") says that every problem in
PPAD satisfies the hypothesis, so this statement gives Theorem 8 for any definition of
PPAD-hardness by polynomial-time search reductions from PPAD, without a formal PPAD class.
Reductions are `SearchReduces` (Cook's Turing machines, correct for every answer); encodings are
binary (`encRatMatrix`). -/
theorem efpo_ppad_hard (Q : TetrisHard.Rows.SearchProblem)
    (hQ : ∀ c : ℝ, 0 < c → SearchReduces Q (ApproxHZProblem c)) :
    SearchReduces Q EFPO := by sorry

end CardinalMatching
