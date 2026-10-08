-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeAdjointAlgebra_gaussLaw_covariant
-- name    : BookProof.ChapterGaugeAdjointAlgebra.gaussLaw_covariant
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T10:52:07.551152+00:00
-- url     : https://prove2.me/theorems/e429df47-bde7-4f48-bae1-b6cbe99ac105
-- title:
--   `BookProof.ChapterGaugeAdjointAlgebra.gaussLaw_covariant` (A dπ π : Fin 3 → L) (θ : L) : ∑ i, (⁅dπ i, θ⁆ + (⁅⁅A i, θ⁆, π i⁆ + ⁅A i, ⁅π i, θ⁆⁆)) = ⁅gaussLaw A...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeAdjointAlgebra`.
--
--   `BookProof.ChapterGaugeAdjointAlgebra.gaussLaw_covariant` (A dπ π : Fin 3 → L) (θ : L) : ∑ i, (⁅dπ i, θ⁆ + (⁅⁅A i, θ⁆, π i⁆ + ⁅A i, ⁅π i, θ⁆⁆)) = ⁅gaussLaw A dπ π, θ⁆
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeAdjointAlgebra.gaussLaw_covariant`.

-- Generated from ChapterGaugeAdjointAlgebra.lean — theorem BookProof.ChapterGaugeAdjointAlgebra.gaussLaw_covariant
import Mathlib
import Definitions.Def_ChapterGaugeAdjointAlgebra
open BookProof.ChapterGaugeAdjointAlgebra




open Finset

variable {L : Type*} [LieRing L]

theorem BookProof.ChapterGaugeAdjointAlgebra.gaussLaw_covariant (A dπ π : Fin 3 → L) (θ : L) :
    ∑ i, (⁅dπ i, θ⁆ + (⁅⁅A i, θ⁆, π i⁆ + ⁅A i, ⁅π i, θ⁆⁆))
      = ⁅gaussLaw A dπ π, θ⁆ := by sorry
