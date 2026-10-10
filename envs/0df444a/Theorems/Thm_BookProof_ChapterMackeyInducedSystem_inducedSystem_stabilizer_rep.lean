-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyInducedSystem_inducedSystem_stabilizer_rep
-- name    : BookProof.ChapterMackeyInducedSystem.inducedSystem_stabilizer_rep
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:52:23.766076+00:00
-- url     : https://prove2.me/theorems/cd95d888-e200-43f0-bef3-af2494287713
-- title:
--   `BookProof.ChapterMackeyInducedSystem.inducedSystem_stabilizer_rep` (L : MulAction.stabilizer G x₀ →* (K ≃ₗᵢ[ℂ] K)) (s : X → G) (hs : ∀ x, s x • x₀ = x) (hs0 : s x₀ = 1) (a...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyInducedSystem`.
--
--   `BookProof.ChapterMackeyInducedSystem.inducedSystem_stabilizer_rep` (L : MulAction.stabilizer G x₀ →* (K ≃ₗᵢ[ℂ] K)) (s : X → G) (hs : ∀ x, s x • x₀ = x) (hs0 : s x₀ = 1) (a : MulAction.stabilizer G x₀) (f : FieldSpace X K) : ((inducedSystem L s hs).U (a : G) f) x₀ = L a (f x₀)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyInducedSystem.inducedSystem_stabilizer_rep`.

-- Generated from ChapterMackeyInducedSystem.lean — theorem BookProof.ChapterMackeyInducedSystem.inducedSystem_stabilizer_rep
import Mathlib
import Definitions.Def_ChapterMackeyInducedSystem
import Definitions.Def_ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem
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

theorem BookProof.ChapterMackeyInducedSystem.inducedSystem_stabilizer_rep (L : MulAction.stabilizer G x₀ →* (K ≃ₗᵢ[ℂ] K)) (s : X → G)
    (hs : ∀ x, s x • x₀ = x) (hs0 : s x₀ = 1) (a : MulAction.stabilizer G x₀)
    (f : FieldSpace X K) :
    ((inducedSystem L s hs).U (a : G) f) x₀ = L a (f x₀) := by sorry
