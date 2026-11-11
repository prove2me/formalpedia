-- Prove2me | Theorems.Thm_FasterExactColoring_ThreeColor_two_valued_elimination
-- name    : FasterExactColoring.ThreeColor.two_valued_elimination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:11:51.745083+00:00
-- url     : https://prove2.me/theorems/9dffe9e7-5de4-4345-9271-1ed61216dc90
-- title:
--   Lemma 3.3 — two-valued variable elimination and locality
-- statement:
--   For arbitrary nonnegative integers $A,n$, let $I$ be an $(A,2)$-CSP and let $v$ be an active variable with at most two available colors. One deterministic polynomial-time program outputs an instance $J$ with exactly $v$ eliminated, satisfying
--   $$I\text{ is satisfiable}\iff J\text{ is satisfiable}.$$
--   All other variable domains and every original constraint not involving $v$ are unchanged. Every added constraint involves only variables that originally shared a constraint with $v$. Zero and one available colors are included. This local reduction supports eliminating the forest leaves without introducing unrelated constraints.
--
--   Differences from the source:
--   - encoding: variables with at most A colors and forbidden constraints → active labels within Fin n, domains in Fin A, and finite lists of forbidden assignments; reason: independent color renaming and inactive padding preserve every instance and eliminate a variable without changing other labels
--   - encoding: uniform algorithm with O* runtime suppressing polynomial factors → one finite log-cost RAM program and uniform positive coefficient and natural polynomial exponent, with charged input, steps and output; reason: the source operations have polynomial bit cost; polynomial simulation overhead preserves the exponential bases
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Lemma 3.3, p. 4 (PDF p. 6)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_RuntimeBounds

namespace FasterExactColoring.ThreeColor

theorem two_valued_elimination :
  ∃ (P : Program) (C : ℝ) (d : ℕ), 0 < C ∧ deterministic P ∧
    ∀ (A n : ℕ) (I : CSP A 2 n) (v : Fin n),
      v ∈ I.active → (I.domain v).card ≤ 2 →
      let x := v.val :: I.code
      runWithin P x (polynomial C d x)
        (fun y => ∃ J : CSP A 2 n, y = J.code ∧ I.localElimination J v) := by sorry

end FasterExactColoring.ThreeColor
