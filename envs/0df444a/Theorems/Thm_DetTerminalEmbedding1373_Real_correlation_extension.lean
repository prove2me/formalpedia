-- Prove2me | Theorems.Thm_DetTerminalEmbedding1373_Real_correlation_extension
-- name    : DetTerminalEmbedding1373.Real.correlation_extension
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:26:29.087457+00:00
-- url     : https://prove2.me/theorems/b2dc6be6-b12f-48c8-9634-7df92bc48816
-- title:
--   Lemma 5.1 — norm-bounded correlation extension
-- statement:
--   Let $x_i\in E_d$ be nonzero, let $v_i=x_i/\|x_i\|$, and set $V=\{v_i,-v_i:i\in[N]\}$. Suppose a linear map $A:E_d\to E_m$ has additive convex-hull distortion at most $\eta$ on $V$. For every $u\in E_d$ there exists $u'\in E_m$ such that
--
--   $$\|u'\|\le\|u\|,\qquad|\langle u',Av_i\rangle-\langle u,v_i\rangle|\le\eta\|u\|\quad(i\in[N]).$$
--
--   The factor $\|u\|$ is retained for arbitrary $u$, with no independence condition on the original vectors. This supplies mathematical feasibility for the correlation objective; it is not a query-time optimization oracle.
--
--   Differences from the source:
--   - encoding: Euclidean spaces and finite indexed vectors or signs → EuclideanSpace over Fin indices and Boolean signs; reason: the Euclidean norm and every real coordinate are retained, with +1 represented by true
--   - generalization: a nonzero indexed family x₁,…,xₙ → natural family sizes including an empty family; reason: for a positive size this is exactly the source; for size zero the correlation clauses are vacuous and u′=0 satisfies the norm bound
-- source:
--   Vladimir Braverman, Kuan Cheng, Jiaqing Zhu, STOC 2027 submission #1373 (October 2026), pp. 18, Lemma 5.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1373.pdf

import Definitions.Def_DetTerminalEmbedding1373_Real_solver

set_option autoImplicit false
open scoped ENNReal

namespace DetTerminalEmbedding1373.Real

/-- Lemma 5.1, p. 18: arbitrary u, with the factor ‖u‖ in both bounds. -/
theorem correlation_extension {N d m : ℕ} (x : Fin N → E d)
    (hx : ∀ i, x i ≠ 0) (A : E d →ₗ[ℝ] E m) (η : ℝ)
    (hA : ConvexHullDistortion A (signedDirections x) η) (u : E d) :
    ∃ u' : E m, ‖u'‖ ≤ ‖u‖ ∧
      ∀ i, |inner ℝ u' (A (direction (x i))) - inner ℝ u (direction (x i))| ≤ η * ‖u‖ := by sorry

end DetTerminalEmbedding1373.Real
