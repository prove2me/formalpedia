-- Prove2me | Theorems.Thm_AccelNewtonDinkelbach_Supplement_theorem_4_11
-- name    : AccelNewtonDinkelbach.Supplement.theorem_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:06:42.122419+00:00
-- url     : https://prove2.me/theorems/6fe40214-0fbf-58a5-bfe4-58b7b5e73544
-- title:
--   Theorem 4.11 — Algorithm 1 terminates in $O(|E(G^{(k)})|)$ iterations in each phase
-- statement:
--   There is one absolute constant $C>0$ with the following property. Let $(G,c,\gamma)$ be any M2VPI system, fix any node order and any execution of Algorithm 3 whose earlier phases did not return, and let phase $k$ reach line 14, starting Algorithm 1 with the Grapevine oracle on the parametric function of $(F_u)$ for $(G^{(k)},c,\gamma)$. Then every execution of Algorithm 1 from that start, for every Grapevine tie-break, has at most
--
--   $$C\,|E(G^{(k)})|$$
--
--   iterates. In particular it terminates, returning a root or NO ROOT, within that many iterations.
--
--   Since line 14 runs only if $y_u<\infty$, the node $u$ has an outgoing arc and $|E(G^{(k)})|\ge 1$, so the bound is never vacuous at $0$.
--
--   Differences from the source:
--   - reading: terminates in O(|E(G^(k))|) iterations → ∃ C > 0, chosen before every system, run and phase, bounding the number N of iterates of every partial execution by C|E(G^(k))|; reason: the uniform absolute-constant meaning of O(·), and a bound on every partial execution is termination within the bound
--   - encoding: an execution of line 14 → the Grapevine-oracle step relation InnerRun reached through Line14Start after phases that continued; reason: retains every tie-break and the label state of Algorithm3Returns
-- source:
--   Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Theorem 4.11 and proof, pp.17–18

import Mathlib
import Definitions.Def_AccelNewtonDinkelbach_Supplement_Algorithm3

namespace AccelNewtonDinkelbach.Supplement

set_option autoImplicit false

/-- **Theorem 4.11 (linear iteration bound in every phase).**
Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Theorem 4.11, p.17.

There is one absolute constant `C > 0` such that for every M2VPI system, every node order, every
execution of phases `0, …, k−1` of Algorithm 3 that continues to phase `k`, and every start of
Algorithm 1 at line 14 of phase `k`: every execution of Algorithm 1 with the Grapevine oracle has
at most `C · |E(G^(k))|` iterates.

**Formalization Note** Bounding the length of every partial execution `s 1, …, s N` asserts
termination as well as the bound: a non-terminating execution would have prefixes of every
length. `∃ C` precedes every instance, so `C` is absolute; the paper gives no numeric constant.
`|E(G^(k))|` is the number of arcs out of the first `k` processed nodes (`k` is 0-indexed here,
so this is `PhaseEdges order (k+1)`), and it is at least 1 whenever line 14 runs. -/
theorem theorem_4_11 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n m : ℕ) (M : M2VPI n m) (order : Fin n → Fin n), Function.Bijective order →
        ∀ (ys : ℕ → Fin n → EReal), ys 0 = (fun _ => ⊤) → ∀ k : Fin n,
          (∀ j : Fin n, j < k → M.PhaseStep order j (ys j.val) (some (ys (j.val + 1)))) →
          ∀ s0 : M2VPI.InnerState n, M.Line14Start order k (ys k.val) s0 →
          ∀ (s : ℕ → M2VPI.InnerState n) (N : ℕ), s 1 = s0 →
            M.InnerRun (M.PhaseEdges order (k.val + 1)) (order k) s N →
            (N : ℝ) ≤ C * M2VPI.activeArcCount (M.PhaseEdges order (k.val + 1)) := by sorry

end AccelNewtonDinkelbach.Supplement
