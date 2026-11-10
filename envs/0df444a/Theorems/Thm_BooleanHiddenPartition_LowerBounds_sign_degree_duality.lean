-- Prove2me | Theorems.Thm_BooleanHiddenPartition_LowerBounds_sign_degree_duality
-- name    : BooleanHiddenPartition.LowerBounds.sign_degree_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T15:21:40.2991+00:00
-- url     : https://prove2.me/theorems/66c1e0f4-6348-410a-a15b-ad1c73ee3c6e
-- title:
--   Fact 6 — Dual characterization of sign degree
-- statement:
--   Let f be any Boolean function on the k-cube, and let d be a natural number. Its sign degree is at least d if and only if there is a probability mass q on the cube whose correlations of f with every parity of size less than d vanish:
--
--   $$d\leq\deg_\pm(f)\quad\Longleftrightarrow\quad\exists q,\ \forall |S|<d,\ \mathbb E_q[f\chi_S]=0.$$
--
--   Both implications and d=0 are included. This is the dual witness assertion used to choose the hard distribution, rather than a definition of sign degree.
--
--   Differences from the source:
--   - encoding: Coordinates in {+1,−1} indexed from 1 → Fin-indexed Bool coordinates with true=−1, and explicit finite averages; reason: The sign map is a bijection and preserves ordered blocks, parities, distributions and all source instances.
--   - encoding: The least degree of a real sign-representing polynomial → MvPolynomial total degree minimized in WithTop Nat; reason: Polynomial interpolation makes the defining set nonempty and the minimum finite; no source function is excluded.
--   - generalization: The positive-arity cube notation of Section 2 → Also k=0; reason: The singleton cube has sign degree zero; the equivalence holds at d=0 and both sides are false for d>0, and every positive arity specializes directly.
-- source:
--   Mark Bun, Joao F. Doriguello, John Kallaugher, Nadezhda Voronova, STOC 2027 submission #1085 (October 2026), p. 14, Fact 6.

import Definitions.Def_BooleanHiddenPartition_LowerBounds_SignDegree

open scoped BigOperators ENNReal
open Classical
set_option autoImplicit false

namespace BooleanHiddenPartition.LowerBounds

noncomputable section

/-- Fact 6, p.14, including d=0 and both directions. -/
theorem sign_degree_duality {k : ℕ} (f : Cube k → Bool) (d : ℕ) :
    (d : WithTop ℕ) ≤ signDegree f ↔
      ∃ q : Cube k → ℝ, IsMass q ∧ moments f q d := by sorry

end

end BooleanHiddenPartition.LowerBounds
