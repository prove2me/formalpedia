-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeAdjointAlgebra_gaussLaw_constraint_surface_invariant
-- name    : BookProof.ChapterGaugeAdjointAlgebra.gaussLaw_constraint_surface_invariant
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T10:53:13.309998+00:00
-- url     : https://prove2.me/theorems/ed57f3f5-0c3f-4c32-a122-63615cd29446
-- title:
--   `BookProof.ChapterGaugeAdjointAlgebra.gaussLaw_constraint_surface_invariant` (A dπ π : Fin 3 → L) (θ : L) (hG : gaussLaw A dπ π = 0) : ∑ i, (⁅dπ i, θ⁆ + (⁅⁅A i, θ⁆, π i⁆...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeAdjointAlgebra`.
--
--   `BookProof.ChapterGaugeAdjointAlgebra.gaussLaw_constraint_surface_invariant` (A dπ π : Fin 3 → L) (θ : L) (hG : gaussLaw A dπ π = 0) : ∑ i, (⁅dπ i, θ⁆ + (⁅⁅A i, θ⁆, π i⁆ + ⁅A i, ⁅π i, θ⁆⁆)) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeAdjointAlgebra.gaussLaw_constraint_surface_invariant`.

-- Generated from ChapterGaugeAdjointAlgebra.lean — theorem BookProof.ChapterGaugeAdjointAlgebra.gaussLaw_constraint_surface_invariant
import Mathlib
import Definitions.Def_ChapterGaugeAdjointAlgebra
open BookProof.ChapterGaugeAdjointAlgebra




open Finset

variable {L : Type*} [LieRing L]

theorem BookProof.ChapterGaugeAdjointAlgebra.gaussLaw_constraint_surface_invariant (A dπ π : Fin 3 → L) (θ : L)
    (hG : gaussLaw A dπ π = 0) :
    ∑ i, (⁅dπ i, θ⁆ + (⁅⁅A i, θ⁆, π i⁆ + ⁅A i, ⁅π i, θ⁆⁆)) = 0 := by sorry
