-- Prove2me | Theorems.Thm_DetTerminalEmbedding1373_Real_sign_pattern_exists
-- name    : DetTerminalEmbedding1373.Real.sign_pattern_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:26:32.180948+00:00
-- url     : https://prove2.me/theorems/a9980143-a4ea-46e2-933e-b0fa15d50867
-- title:
--   Lemma 4.2 — existence of a sign pattern
-- statement:
--   For unit vectors $v_j\in E_d$ and tolerances $0<\delta_j\le1$, suppose $\sum_j2e^{-m\delta_j^2/8}<1/2$. There is one sign matrix $\Sigma\in\{\pm1\}^{m\times d}$, with $A=\Sigma/\sqrt m$, such that
--
--   $$|\|Av_j\|^2-1|<\delta_j\qquad\text{for every }j\in[L].$$
--
--   All tests share the same matrix and retain their individual strict tolerances. This result supplies the existence part of deterministic signing.
--
--   Differences from the source:
--   - encoding: Euclidean spaces and finite indexed vectors or signs → EuclideanSpace over Fin indices and Boolean signs; reason: the Euclidean norm and every real coordinate are retained, with +1 represented by true
-- source:
--   Vladimir Braverman, Kuan Cheng, Jiaqing Zhu, STOC 2027 submission #1373 (October 2026), pp. 12, Lemma 4.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1373.pdf

import Definitions.Def_DetTerminalEmbedding1373_Real_potential

set_option autoImplicit false
open scoped ENNReal

namespace DetTerminalEmbedding1373.Real

/-- Lemma 4.2, p. 12: every tolerance and the strict conclusion are retained. -/
theorem sign_pattern_exists {L m d : ℕ} (v : Fin L → E d) (δ : Fin L → ℝ)
    (hv : ∀ j, ‖v j‖ = 1) (hδ : ∀ j, 0 < δ j ∧ δ j ≤ 1)
    (hbudget : TestBudget m δ) :
    ∃ σ : Fin m → Fin d → Bool, ∀ j, |‖signProjection σ (v j)‖ ^ 2 - 1| < δ j := by sorry

end DetTerminalEmbedding1373.Real
