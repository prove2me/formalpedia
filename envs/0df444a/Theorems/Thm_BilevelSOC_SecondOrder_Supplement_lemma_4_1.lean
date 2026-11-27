-- Prove2me | Theorems.Thm_BilevelSOC_SecondOrder_Supplement_lemma_4_1
-- name    : BilevelSOC.SecondOrder.Supplement.lemma_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T07:44:21.305478+00:00
-- url     : https://prove2.me/theorems/b39d6bd0-e0d3-46ed-b0d3-6822e13ac525
-- title:
--   Lemma 4.1 — Tangent-cone criterion for first-order growth and strict local optimality
-- statement:
--   Let $D=(F,f,G,g)$ satisfy the standing $C^2$ assumptions, let $M$ be its full bilevel feasible set, and let $z\in M$. If
--
--   $$d\in T_M(z),\quad DF(z)d\le0\quad\Longrightarrow\quad d=0,$$
--
--   then the first-order growth condition holds at $z$: there are a neighborhood $U$ and $C>0$ with $F(a)\ge F(z)+C\|a-z\|$ for all $a\in M\cap U$. Moreover, $z$ is a strict local minimizer. The cone is the sequential Bouligand tangent cone. This support retains both growth and strictness and requires no global closedness of $M$.
--
--   Differences from the source:
--   - encoding: Euclidean coordinates and gradients, indexed from 1 → published E and Y spaces, uncurried pairs, Fin indices from 0, and Fréchet derivatives or partial Euclidean gradients; reason: the same finite-dimensional data; derivative evaluation equals the gradient pairing under Standing D
--   - encoding: first-order growth in the Euclidean norm of the joint pair → published GrowthCondition with Lean’s product norm; reason: finite-dimensional equivalent norms give exactly the same existence of a positive growth constant; no numerical constant is fixed
-- source:
--   Mehlitz & Zemkoho, Sufficient Optimality Conditions in Bilevel Programming, arXiv:1911.01647v1, p. 10, Lemma 4.1

import Mathlib
import Definitions.Def_BilevelSOC_SecondOrder_Supplement_FirstOrder
open scoped Topology

namespace BilevelSOC.SecondOrder.Supplement
theorem lemma_4_1 {n m p q : ℕ} (D : Data n m p q) (z : E n × Y m)
    (hStanding : Standing D) (hfeas : z ∈ feasSet D)
    (hexclude : ∀ d ∈ tangentCone (feasSet D) z, fderiv ℝ D.F z d ≤ 0 → d = 0) :
    GrowthCondition D.F (feasSet D) z 1 ∧ StrictLocalMin D.F (feasSet D) z := by sorry
end BilevelSOC.SecondOrder.Supplement
