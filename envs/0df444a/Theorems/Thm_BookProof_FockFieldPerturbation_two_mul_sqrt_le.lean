-- Prove2me | Theorems.Thm_BookProof_FockFieldPerturbation_two_mul_sqrt_le
-- name    : BookProof.FockFieldPerturbation.two_mul_sqrt_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:35:38.001025+00:00
-- url     : https://prove2.me/theorems/37bedcb3-c897-43fd-8df5-29ca9074774d
-- title:
--   `BookProof.FockFieldPerturbation.two_mul_sqrt_le` {c n N t : ℝ} (hN : 0 ≤ N) (ht : 0 < t) : 2 * c * Real.sqrt N * n ≤ t * N + c ^ 2 / t * n ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockFieldPerturbation`.
--
--   `BookProof.FockFieldPerturbation.two_mul_sqrt_le` {c n N t : ℝ} (hN : 0 ≤ N) (ht : 0 < t) : 2 * c * Real.sqrt N * n ≤ t * N + c ^ 2 / t * n ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.FockFieldPerturbation.two_mul_sqrt_le`.

-- Generated from ChapterFockFieldPerturbation.lean — theorem BookProof.FockFieldPerturbation.two_mul_sqrt_le
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockInteractionStability
import Mathlib
import Definitions.Def_ChapterFockFieldPerturbation
open BookProof.FockFieldPerturbation


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability

theorem BookProof.FockFieldPerturbation.two_mul_sqrt_le {c n N t : ℝ} (hN : 0 ≤ N) (ht : 0 < t) :
    2 * c * Real.sqrt N * n ≤ t * N + c ^ 2 / t * n ^ 2 := by sorry
