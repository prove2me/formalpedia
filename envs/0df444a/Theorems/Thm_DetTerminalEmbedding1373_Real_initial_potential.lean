-- Prove2me | Theorems.Thm_DetTerminalEmbedding1373_Real_initial_potential
-- name    : DetTerminalEmbedding1373.Real.initial_potential
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:26:25.985903+00:00
-- url     : https://prove2.me/theorems/328b451f-4c48-4835-81c3-3f7548e080a0
-- title:
--   Claim 4.4 — initial Gaussian potential
-- statement:
--   Let $v_j\in E_d$ be unit vectors and let $0<\delta_j\le1$ for every test $j\in[L]$. If the row count $m$ satisfies $\sum_j2e^{-m\delta_j^2/8}<1/2$, then
--
--   $$\Phi(\varnothing)<\tfrac12.$$
--
--   Here the empty pattern leaves every coordinate Gaussian. This is the initial bound for the same total potential used by the complete-pattern certificate.
--
--   Differences from the source:
--   - encoding: Euclidean spaces and finite indexed vectors or signs → EuclideanSpace over Fin indices and Boolean signs; reason: the Euclidean norm and every real coordinate are retained, with +1 represented by true
--   - encoding: Gaussian expectations over the unassigned coordinates → extended nonnegative integrals over independent Gaussian coordinates with fixed entries overwritten; reason: the unused coordinates integrate to one; infinite expectations remain infinite, and the stated upper bounds force finiteness
-- source:
--   Vladimir Braverman, Kuan Cheng, Jiaqing Zhu, STOC 2027 submission #1373 (October 2026), pp. 13, Claim 4.4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1373.pdf

import Definitions.Def_DetTerminalEmbedding1373_Real_potential

set_option autoImplicit false
open scoped ENNReal

namespace DetTerminalEmbedding1373.Real

/-- Claim 4.4, p. 13, including the setup and (10). -/
theorem initial_potential {L m d : ℕ} (v : Fin L → E d) (δ : Fin L → ℝ)
    (hv : ∀ j, ‖v j‖ = 1) (hδ : ∀ j, 0 < δ j ∧ δ j ≤ 1)
    (hbudget : TestBudget m δ) :
    totalPotential (m := m) v δ (fun _ => none) < (1 / 2 : ℝ≥0∞) := by sorry

end DetTerminalEmbedding1373.Real
