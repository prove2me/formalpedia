-- Prove2me | Theorems.Thm_FasterExactColoring_ThreeColor_Supplement_branching_reductions
-- name    : FasterExactColoring.ThreeColor.Supplement.branching_reductions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:54:56.530585+00:00
-- url     : https://prove2.me/theorems/af75a347-e56a-43f0-9e87-6031917f10ea
-- title:
--   Lemma 5.7 (used in the proof of Theorem 1.3) — branching budget and correctness
-- statement:
--   Fix $r>1$ and nonnegative measure weights with $\omega_0=0$, $\omega_i=1$ for $i\ge3$, satisfying every linear and branching constraint of Appendix D. There are one deterministic finite program and uniform constants $C>0,d\in\mathbb N$ such that for each valid nonterminal restricted instance $P=(G,I,S)$ it generates a finite list $P_j=(G,I_j,S_j)$ of valid restricted instances. All four requirements hold:
--   $$\sum_j r^{\mu(P_j)}\le r^{\mu(P)},\qquad
--    P\text{ is colorable}\ \Longleftrightarrow\ \exists j,\ P_j\text{ is colorable},$$
--   $$|U_j|<|U|\quad\text{for every }j,\qquad
--    \text{generation cost}\le C(\operatorname{inputCost}(P)+1)^d(t+1).$$
--   The execution outputs exactly the encoded $t$ children, and each child retains the same graph $G$. An empty list is permitted only when the equivalence establishes that $P$ is unsatisfiable. This is this paper's restatement of the cited branching lemma, including budget, both correctness directions, strict decrease and polynomial overhead per child.
--
--   Differences from the source:
--   - encoding: branching reductions generate the subinstances with polynomial overhead per subinstance → one deterministic finite program outputs the complete list of changed I,S sets on the same graph, with cost poly(inputCost)*(t+1); reason: the list encoding charges generation and output, also handling an empty rejecting branch; all four source guarantees remain conclusions
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Lemma 5.7, p. 15 (PDF p. 17)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_Supplement_Measure
import Definitions.Def_FasterExactColoring_ThreeColor_Supplement_TerminalBounds

set_option autoImplicit false

namespace FasterExactColoring.ThreeColor.Supplement

theorem branching_reductions (r : ℝ) (w : Weights) (hr : 1 < r) (hw : appendixD r w) :
  ∃ (A : Program) (C : ℝ) (d : ℕ), 0 < C ∧ deterministic A ∧
    ∀ (n : ℕ) (P : Restricted n), P.valid → ¬ P.terminal →
      ∃ L : List (Finset (Fin n) × Finset (Fin n)),
        (∀ IS ∈ L, (child P IS).valid ∧ (child P IS).U.card < P.U.card) ∧
        ((L.map (fun IS => r^(measure w (child P IS)))).sum ≤ r^(measure w P)) ∧
        (P.colorable ↔ ∃ IS ∈ L, (child P IS).colorable) ∧
        runWithin A P.code (polynomial C d P.code * (L.length+1 : ℕ))
          (fun y => y = childrenCode L) := by sorry

end FasterExactColoring.ThreeColor.Supplement
