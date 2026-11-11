-- Prove2me | Theorems.Thm_FixedPolyominoSquare_SquareCounting_boundary_amplification
-- name    : FixedPolyominoSquare.SquareCounting.boundary_amplification
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:35:03.120334+00:00
-- url     : https://prove2.me/theorems/f89162c5-9f17-4f88-ac84-659b438374c2
-- title:
--   Theorem 5.1 — boundary amplification
-- statement:
--   For every integer $Q\geq1$, use the finite four-track amplifier defined by the source's atomic colour rules. For every $n\geq2$, its open square tilings have a unique side-activity class, and
--
--   $$a_{\rm full}(n)=Q^{4n-4},\qquad a_S(n)\leq Q^{3n-2}\quad(S\subsetneq\{W,E,S,N\}).$$
--
--   For every $n\geq1$, adjoining the private-colour dummy increases the total open square count by exactly one. The full class includes one shared index at each active corner. The proper-class bounds and the private dummy are both retained, rather than only the full-frame count.
--
--   **Formalization Note** The boundary-class predicate tests each boundary cell on the indicated side. Colour tuples and tile data are enumerated bijectively into finite types, and inactive indices use the zero-based representative of the source's index one.
--
--   Differences from the source:
--   - encoding: indices 1 through Q with inactive index 1 and four named side-activity tracks → Fin Q with inactive index 0, bijectively enumerated atomic colour tuples and an explicit unique boundary-class predicate; reason: the relabeling preserves every type, shared corner label, boundary class and tiling; the class predicate spells out the side constancy established on p. 10
--   - generalization: there is a fixed Wang system with four side-activity tracks, and the dummy sentence follows the n ≥ 2 clause → the source's own amplifier construction (pp. 10–11) satisfies every clause, every matching tiling lies in exactly one side class, and the dummy clause holds for every n ≥ 1; reason: a named system with these properties implies the existential, and the n ≥ 1 dummy clause contains the n ≥ 2 reading (at n = 0 the empty square has one tiling for both systems, so n ≥ 1 is the full range)
-- source:
--   Qiuyu Chen, Ba'ao Xie, STOC 2027 submission #219 (October 2026), p. 10, Theorem 5.1; pp. 10–11, construction

import Definitions.Def_FixedPolyominoSquare_SquareCounting_Amplifier

namespace FixedPolyominoSquare.SquareCounting

/-- Chen--Xie, Theorem 5.1, p. 10, for the actual four coupled activity tracks.
One label at a shared active corner is counted only once. The dummy clause is
stated for every nonempty square `n ≥ 1`. -/
theorem boundary_amplification (Q : ℕ) (hQ : 1 ≤ Q) :
    (∀ n : ℕ, 2 ≤ n →
      (∀ f : WangAssignment (amplifier Q) (square n),
        WangMatches (amplifier Q) (square n) f → ∃! η, InActivityClass Q n η f) ∧
      activityCount Q n (fun _ => true) = Q ^ (4 * n - 4) ∧
      (∀ η : Fin 4 → Bool, η ≠ (fun _ => true) →
        activityCount Q n η ≤ Q ^ (3 * n - 2))) ∧
    (∀ n : ℕ, 1 ≤ n →
      aSquare (withDummy (amplifier Q)) n = aSquare (amplifier Q) n + 1) := by sorry

end FixedPolyominoSquare.SquareCounting
