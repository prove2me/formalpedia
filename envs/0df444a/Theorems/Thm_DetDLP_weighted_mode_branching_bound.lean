-- Prove2me | Theorems.Thm_DetDLP_weighted_mode_branching_bound
-- name    : DetDLP.weighted_mode_branching_bound
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T12:13:27.317237+00:00
-- url     : https://prove2.me/theorems/5976fe47-6532-4cb2-ad05-08437bfa69a0
-- title:
--   Weighted mode count and scalar recursion branching
-- statement:
--   Let a finite family of variables have positive integral weights, with at most $B$ variables of any one weight. For $p,B\ge1$, the number $N$ of exponent vectors of total weight less than $p$ satisfies
--   $$N\le \exp(3\sqrt{Bp}).$$
--   In particular, if $B\le 6M/D$ and the child precision obeys $p\le C M D/u$, then $N\le \exp(3\sqrt{6C}\,M/\sqrt u)$. This is the mode enumeration bound at one contraction node.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026. Section 5.1, weighted mode enumeration, and Section 5.2, branching at one active node.

import Mathlib

set_option autoImplicit false

namespace DetDLP

theorem weighted_mode_branching_bound {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℕ) (B p : ℕ)
    (hm : ∀ j, (Finset.univ.filter fun i => w i=j).card ≤ B)
    (hB : 0 < B) (hp : 0 < p) (M D u C : ℝ) (hM : 0 ≤ M) (hD : 0 < D)
    (hu : 0 < u) (hC : 0 ≤ C) (hBD : (B:ℝ) ≤ 6*M/D) (hP : (p:ℝ) ≤ C*M*D/u) :
    let N := (Finset.univ.filter fun β : ι → Fin p => (∑ i, (w i+1)*(β i).val) < p).card
    (N:ℝ) ≤ Real.exp (3*Real.sqrt ((B:ℝ)*p)) ∧
      (N:ℝ) ≤ Real.exp (3*Real.sqrt (6*C)*M/Real.sqrt u) := by sorry
end DetDLP
