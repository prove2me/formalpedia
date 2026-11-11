-- Prove2me | Theorems.Thm_DetTerminalEmbedding1373_Real_objective_lipschitz
-- name    : DetTerminalEmbedding1373.Real.objective_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:26:42.703844+00:00
-- url     : https://prove2.me/theorems/62997a94-e2c7-41f3-aea0-311310ad38ac
-- title:
--   Claim 5.3 — the correlation objective is 2-Lipschitz
-- statement:
--   For a nonempty finite family of vectors $a_i\in E_m$ with $\|a_i\|\le2$ and arbitrary real scalars $c_i$, define $f(w)=\max_i|\langle w,a_i\rangle-c_i|$. Then
--
--   $$|f(w)-f(v)|\le2\|w-v\|\qquad(w,v\in E_m).$$
--
--   The correlation data in equation (33) satisfy the norm bound under the section's convex-hull assumption. This is the source's same Lipschitz conclusion in a reusable finite-objective form.
--
--   Differences from the source:
--   - encoding: Euclidean spaces and finite indexed vectors or signs → EuclideanSpace over Fin indices and Boolean signs; reason: the Euclidean norm and every real coordinate are retained, with +1 represented by true
--   - generalization: the geometric correlation objective of (33)–(34) → any nonempty finite absolute-affine maximum with all normal vectors of norm at most 2; reason: the source setup gives norm at most 1+η≤3/2, so it is an instance without adding any source hypothesis
-- source:
--   Vladimir Braverman, Kuan Cheng, Jiaqing Zhu, STOC 2027 submission #1373 (October 2026), pp. 19, Claim 5.3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1373.pdf

import Definitions.Def_DetTerminalEmbedding1373_Real_solver

set_option autoImplicit false
open scoped ENNReal

namespace DetTerminalEmbedding1373.Real

/-- Claim 5.3, p. 19, in its finite affine-objective form. The geometric setup
implies ‖aᵢ‖ ≤ 1+η < 2; no independence or feasible optimum is assumed. -/
theorem objective_lipschitz {N m : ℕ} (hN : 0 < N)
    (a : Fin N → E m) (c : Fin N → ℝ) (ha : ∀ i, ‖a i‖ ≤ 2) :
    ∀ w v : E m, |objective a c w - objective a c v| ≤ 2 * ‖w - v‖ := by sorry

end DetTerminalEmbedding1373.Real
