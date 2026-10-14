-- Prove2me | Theorems.Thm_BookProof_ChapterUnitaryTransport_transported_position_group
-- name    : BookProof.ChapterUnitaryTransport.transported_position_group
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T20:39:11.749705+00:00
-- url     : https://prove2.me/theorems/7f2b6872-743b-4166-a9f6-453e55e7a3ae
-- title:
--   `BookProof.ChapterUnitaryTransport.transported_position_group` (f : ℤ → ℝ) (W : L2Z ≃ₗᵢ[ℂ] K) (s t : ℝ) (y : K) : transportUnitary W (phaseUnitary f (s + t)) y = transportUnitary W
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUnitaryTransport`.
--
--   `BookProof.ChapterUnitaryTransport.transported_position_group` (f : ℤ → ℝ) (W : L2Z ≃ₗᵢ[ℂ] K) (s t : ℝ) (y : K) : transportUnitary W (phaseUnitary f (s + t)) y = transportUnitary W (phaseUnitary f s) (transportUnitary W (phaseUnitary f t) y)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterUnitaryTransport.transported_position_group`.

-- Generated from ChapterUnitaryTransport.lean — theorem BookProof.ChapterUnitaryTransport.transported_position_group
import Mathlib
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterUnboundedPosition
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterUnboundedPosition
open BookProof.ChapterUnitaryTransport


open scoped InnerProductSpace


variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem BookProof.ChapterUnitaryTransport.transported_position_group (f : ℤ → ℝ) (W : L2Z ≃ₗᵢ[ℂ] K) (s t : ℝ) (y : K) :
    transportUnitary W (phaseUnitary f (s + t)) y
      = transportUnitary W (phaseUnitary f s) (transportUnitary W (phaseUnitary f t) y) := by sorry
