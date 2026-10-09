-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeAdjointAlgebra_weylEnergy_gauge_invariant
-- name    : BookProof.ChapterGaugeAdjointAlgebra.weylEnergy_gauge_invariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T10:52:56.810153+00:00
-- url     : https://prove2.me/theorems/e8772a5b-057f-4fba-ac5f-0d07d4540888
-- title:
--   `BookProof.ChapterGaugeAdjointAlgebra.weylEnergy_gauge_invariant` {κ : L → L → ℝ} (hinv : ∀ x y z : L, κ ⁅x, z⁆ y + κ x ⁅y, z⁆ = 0) (hsymm : ∀ x y : L, κ x y = κ y x) (π :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeAdjointAlgebra`.
--
--   `BookProof.ChapterGaugeAdjointAlgebra.weylEnergy_gauge_invariant` {κ : L → L → ℝ} (hinv : ∀ x y z : L, κ ⁅x, z⁆ y + κ x ⁅y, z⁆ = 0) (hsymm : ∀ x y : L, κ x y = κ y x) (π : Fin 3 → L) (B : Fin 3 → Fin 3 → L) (θ : L) : (∑ i, κ ⁅π i, θ⁆ (π i)) + (1 / 2) * ∑ i, ∑ j, κ ⁅B i j, θ⁆ (B i j) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeAdjointAlgebra.weylEnergy_gauge_invariant`.

-- Generated from ChapterGaugeAdjointAlgebra.lean — theorem BookProof.ChapterGaugeAdjointAlgebra.weylEnergy_gauge_invariant
import Mathlib
import Definitions.Def_ChapterGaugeAdjointAlgebra
open BookProof.ChapterGaugeAdjointAlgebra




open Finset

variable {L : Type*} [LieRing L]

theorem BookProof.ChapterGaugeAdjointAlgebra.weylEnergy_gauge_invariant {κ : L → L → ℝ}
    (hinv : ∀ x y z : L, κ ⁅x, z⁆ y + κ x ⁅y, z⁆ = 0)
    (hsymm : ∀ x y : L, κ x y = κ y x)
    (π : Fin 3 → L) (B : Fin 3 → Fin 3 → L) (θ : L) :
    (∑ i, κ ⁅π i, θ⁆ (π i)) + (1 / 2) * ∑ i, ∑ j, κ ⁅B i j, θ⁆ (B i j) = 0 := by sorry
