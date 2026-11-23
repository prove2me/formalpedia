-- Prove2me | Theorems.Thm_BilevelSOC_SecondOrder_Supplement_theorem_4_18
-- name    : BilevelSOC.SecondOrder.Supplement.theorem_4_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:53:14.35359+00:00
-- url     : https://prove2.me/theorems/09586cae-27a9-4ab7-a7a9-4f84921fd599
-- title:
--   Theorem 4.18 — Full complementarity exclusion criterion for strict local optimality
-- statement:
--   Let $D=(F,f,G,g)$ satisfy the standing $C^2$ assumptions, with convex lower objective and constraint sections and the exact KKT characterization of $S$. Fix a bilevel feasible pair $z$ and a lower multiplier $\bar\lambda\in\Lambda(z)$ satisfying the complete strict Mangasarian–Fromovitz implication (4.9). Put $L=f+\bar\lambda^Tg$ and use the three complementarity index sets $I^{0-},I^{+0},I^{00}$. Suppose
--
--   $$\begin{gathered}DF(z)d\le0,\quad DG_i(z)d\le0\ (i\in\bar I^G),\\
--   D(\nabla_yL)(z)d+\sum_i(\delta_\lambda)_i\nabla_yg_i(z)=0,\\
--   (\delta_\lambda)_i=0\ (i\in I^{0-}),\quad Dg_i(z)d=0\ (i\in I^{+0}),\\
--   0\le(\delta_\lambda)_i\perp Dg_i(z)d\le0\ (i\in I^{00})
--   \end{gathered}$$
--
--   has only the zero augmented solution $(d,\delta_\lambda)=0$. Then $z$ is a strict local minimizer of the bilevel program. This KKT companion uses the full nontrivial-triple exclusion printed in the theorem. Its convexity and KKT-equivalence premise includes all the instances of Assumption 4.14 without choosing a stronger named CQ.
--
--   Differences from the source:
--   - encoding: Euclidean coordinates and gradients, indexed from 1 → published E and Y spaces, uncurried pairs, Fin indices from 0, and Fréchet derivatives or partial Euclidean gradients; reason: the same finite-dimensional data; derivative evaluation equals the gradient pairing under Standing D
--   - generalization: convex lower data and a lower CQ everywhere on gph K (Assumption 4.14) → convex lower data and exact global KKT equivalence, without selecting a named CQ; reason: the source immediately states this consequence on p. 16 and uses it to identify M as the projected KKT set; the weaker premise includes every source instance
-- source:
--   Mehlitz & Zemkoho, Sufficient Optimality Conditions in Bilevel Programming, arXiv:1911.01647v1, p. 17, Theorem 4.18

import Mathlib
import Definitions.Def_BilevelSOC_SecondOrder_Supplement_Complementarity
open scoped Topology

namespace BilevelSOC.SecondOrder.Supplement
theorem theorem_4_18 {n m p q : ℕ} (D : Data n m p q) (z : E n × Y m)
    (lam : Fin q → ℝ) (hStanding : Standing D) (hfeas : z ∈ feasSet D)
    (hconvexCQ : ConvexKKTExact D) (hlam : lam ∈ multipliers D z)
    (hstrict : StrictMFCQ D z lam)
    (hexclude : ∀ w ∈ kktLinCone D z lam, fderiv ℝ D.F z w.1 ≤ 0 → w = 0) :
    StrictLocalMin D.F (feasSet D) z := by sorry
end BilevelSOC.SecondOrder.Supplement
