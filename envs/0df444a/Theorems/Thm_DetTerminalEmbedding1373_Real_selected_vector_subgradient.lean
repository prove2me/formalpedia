-- Prove2me | Theorems.Thm_DetTerminalEmbedding1373_Real_selected_vector_subgradient
-- name    : DetTerminalEmbedding1373.Real.selected_vector_subgradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:26:39.613617+00:00
-- url     : https://prove2.me/theorems/93958bf6-9b1b-45f1-98ba-51194ee88f83
-- title:
--   Claim 5.4 — the selected vector is a subgradient
-- statement:
--   For a nonempty finite family $a_i\in E_m$, arbitrary scalars $c_i$, and $f(w)=\max_i|\langle w,a_i\rangle-c_i|$, choose the earliest maximizing index and let $g(w)$ be its signed normal, taking zero when the residual is zero. For every $w,v\in E_m$,
--
--   $$f(v)\ge f(w)+\langle g(w),v-w\rangle.$$
--
--   Specializing to $w=w_t$ gives exactly the subgradient inequality for the source's selected vector $g_t$. No norm bound or feasible optimum is needed for this inequality.
--
--   Differences from the source:
--   - encoding: Euclidean spaces and finite indexed vectors or signs → EuclideanSpace over Fin indices and Boolean signs; reason: the Euclidean norm and every real coordinate are retained, with +1 represented by true
--   - generalization: the selected subgradient at an iterate of the geometric correlation problem → the same selection rule at any point of any nonempty finite absolute-affine maximum; reason: the geometric objective and all its iterates are instances, and the omitted geometric assumptions are not used by the subgradient inequality
-- source:
--   Vladimir Braverman, Kuan Cheng, Jiaqing Zhu, STOC 2027 submission #1373 (October 2026), pp. 19, Claim 5.4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1373.pdf

import Definitions.Def_DetTerminalEmbedding1373_Real_solver

set_option autoImplicit false
open scoped ENNReal

namespace DetTerminalEmbedding1373.Real

/-- Claim 5.4, p. 19, for every evaluation point of the same objective. -/
theorem selected_vector_subgradient {N m : ℕ} (hN : 0 < N)
    (a : Fin N → E m) (c : Fin N → ℝ) (w : E m) :
    ∀ v : E m, objective a c v ≥ objective a c w +
      inner ℝ (selectedSubgradient a c w) (v - w) := by sorry

end DetTerminalEmbedding1373.Real
