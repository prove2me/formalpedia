-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeAdjointAlgebra_adjVar_eq_zero_of_central
-- name    : BookProof.ChapterGaugeAdjointAlgebra.adjVar_eq_zero_of_central
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T10:52:02.05619+00:00
-- url     : https://prove2.me/theorems/d78f7300-a2bf-49e3-9bba-e5e5476052e6
-- title:
--   `BookProof.ChapterGaugeAdjointAlgebra.adjVar_eq_zero_of_central` {X : L} (hX : ∀ θ : L, ⁅X, θ⁆ = 0) (θ : L) : adjVar θ X = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeAdjointAlgebra`.
--
--   `BookProof.ChapterGaugeAdjointAlgebra.adjVar_eq_zero_of_central` {X : L} (hX : ∀ θ : L, ⁅X, θ⁆ = 0) (θ : L) : adjVar θ X = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeAdjointAlgebra.adjVar_eq_zero_of_central`.

-- Generated from ChapterGaugeAdjointAlgebra.lean — theorem BookProof.ChapterGaugeAdjointAlgebra.adjVar_eq_zero_of_central
import Mathlib
import Definitions.Def_ChapterGaugeAdjointAlgebra
open BookProof.ChapterGaugeAdjointAlgebra




open Finset

variable {L : Type*} [LieRing L]

theorem BookProof.ChapterGaugeAdjointAlgebra.adjVar_eq_zero_of_central {X : L} (hX : ∀ θ : L, ⁅X, θ⁆ = 0) (θ : L) :
    adjVar θ X = 0 := by sorry
