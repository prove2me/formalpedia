-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeAdjointAlgebra_covariantDeriv_covariant
-- name    : BookProof.ChapterGaugeAdjointAlgebra.covariantDeriv_covariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T10:52:15.271338+00:00
-- url     : https://prove2.me/theorems/afe6345b-f35a-4e40-baca-069f79cebb6d
-- title:
--   `BookProof.ChapterGaugeAdjointAlgebra.covariantDeriv_covariant` (A dX dθ : Fin 3 → L) (X θ : L) (i : Fin 3) : (⁅dX i, θ⁆ + ⁅X, dθ i⁆) + (⁅gaugeVarA A dθ θ i, X⁆ + ⁅A i,...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeAdjointAlgebra`.
--
--   `BookProof.ChapterGaugeAdjointAlgebra.covariantDeriv_covariant` (A dX dθ : Fin 3 → L) (X θ : L) (i : Fin 3) : (⁅dX i, θ⁆ + ⁅X, dθ i⁆) + (⁅gaugeVarA A dθ θ i, X⁆ + ⁅A i, ⁅X, θ⁆⁆) = ⁅covariantDeriv A dX X i, θ⁆
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeAdjointAlgebra.covariantDeriv_covariant`.

-- Generated from ChapterGaugeAdjointAlgebra.lean — theorem BookProof.ChapterGaugeAdjointAlgebra.covariantDeriv_covariant
import Mathlib
import Definitions.Def_ChapterGaugeAdjointAlgebra
open BookProof.ChapterGaugeAdjointAlgebra




open Finset

variable {L : Type*} [LieRing L]

theorem BookProof.ChapterGaugeAdjointAlgebra.covariantDeriv_covariant (A dX dθ : Fin 3 → L) (X θ : L) (i : Fin 3) :
    (⁅dX i, θ⁆ + ⁅X, dθ i⁆) + (⁅gaugeVarA A dθ θ i, X⁆ + ⁅A i, ⁅X, θ⁆⁆)
      = ⁅covariantDeriv A dX X i, θ⁆ := by sorry
