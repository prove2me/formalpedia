-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyInducedSystem_inducedSystem_fibre
-- name    : BookProof.ChapterMackeyInducedSystem.inducedSystem_fibre
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:51:54.180817+00:00
-- url     : https://prove2.me/theorems/d8804ace-dfed-47ab-a309-22269f668b7e
-- title:
--   `BookProof.ChapterMackeyInducedSystem.inducedSystem_fibre` (L : MulAction.stabilizer G x₀ →* (K ≃ₗᵢ[ℂ] K)) (s : X → G) (hs : ∀ x, s x • x₀ = x) (f : FieldSpace X K) : (inducedSyste
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyInducedSystem`.
--
--   `BookProof.ChapterMackeyInducedSystem.inducedSystem_fibre` (L : MulAction.stabilizer G x₀ →* (K ≃ₗᵢ[ℂ] K)) (s : X → G) (hs : ∀ x, s x • x₀ = x) (f : FieldSpace X K) : (inducedSystem L s hs).p x₀ f = f ↔ ∀ x, x ≠ x₀ → f x = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyInducedSystem.inducedSystem_fibre`.

-- Generated from ChapterMackeyInducedSystem.lean — theorem BookProof.ChapterMackeyInducedSystem.inducedSystem_fibre
import Definitions.Def_ChapterMackeyImprimitivity
import Mathlib
import Definitions.Def_ChapterMackeyInducedSystem
open BookProof.ChapterMackeyInducedSystem


open scoped InnerProductSpace
open Finset


open BookProof.ChapterMackeyImprimitivity

variable {G : Type*} [Group G] {X : Type*} [Fintype X] [DecidableEq X] [MulAction G X]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
variable {x₀ : X}

variable {L : MulAction.stabilizer G x₀ →* (K ≃ₗᵢ[ℂ] K)} {s : X → G}
variable (L s)
variable {L s}
variable (X K) in

theorem BookProof.ChapterMackeyInducedSystem.inducedSystem_fibre (L : MulAction.stabilizer G x₀ →* (K ≃ₗᵢ[ℂ] K)) (s : X → G)
    (hs : ∀ x, s x • x₀ = x) (f : FieldSpace X K) :
    (inducedSystem L s hs).p x₀ f = f ↔ ∀ x, x ≠ x₀ → f x = 0 := by sorry
