-- Prove2me | Theorems.Thm_DetTerminalEmbedding1373_Real_potential_certifies_tests
-- name    : DetTerminalEmbedding1373.Real.potential_certifies_tests
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:26:18.083203+00:00
-- url     : https://prove2.me/theorems/eea00396-a21d-49ea-957c-2840e38cc42c
-- title:
--   Claim 4.3 — complete potential certifies every test
-- statement:
--   Let $v\in E_d$ have norm one, let $0<\delta\le1$, and let $\Sigma\in\{\pm1\}^{m\times d}$ be a complete sign assignment. With $A=\Sigma/\sqrt m$ and the potentials of equation (14),
--
--   $$\Psi_v^+(\Sigma)+\Psi_v^-(\Sigma)<1\quad\Longrightarrow\quad|\|Av\|^2-1|<\delta.$$
--
--   This is the per-test certificate used after all signs have been assigned. It does not assume the desired norm guarantee or a good projection.
--
--   Differences from the source:
--   - encoding: Euclidean spaces and finite indexed vectors or signs → EuclideanSpace over Fin indices and Boolean signs; reason: the Euclidean norm and every real coordinate are retained, with +1 represented by true
--   - encoding: Gaussian expectations over the unassigned coordinates → extended nonnegative integrals over independent Gaussian coordinates with fixed entries overwritten; reason: the unused coordinates integrate to one; infinite expectations remain infinite, and the stated upper bounds force finiteness
-- source:
--   Vladimir Braverman, Kuan Cheng, Jiaqing Zhu, STOC 2027 submission #1373 (October 2026), pp. 13, Claim 4.3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1373.pdf

import Definitions.Def_DetTerminalEmbedding1373_Real_potential

set_option autoImplicit false
open scoped ENNReal

namespace DetTerminalEmbedding1373.Real

/-- Claim 4.3, p. 13. The selected test is a unit vector; its completed
potential is the expectation over no remaining coordinates. -/
theorem potential_certifies_tests {m d : ℕ} (v : E d) (δ : ℝ)
    (hv : ‖v‖ = 1) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (σ : Fin m → Fin d → Bool)
    (hψ : psi v δ (fun ij => some (σ ij.1 ij.2)) true +
      psi v δ (fun ij => some (σ ij.1 ij.2)) false < 1) :
    |‖signProjection σ v‖ ^ 2 - 1| < δ := by sorry

end DetTerminalEmbedding1373.Real
