-- Prove2me | Theorems.Thm_BookProof_ChapterMackeyInducedSystem_mackey_correspondence
-- name    : BookProof.ChapterMackeyInducedSystem.mackey_correspondence
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:52:38.888869+00:00
-- url     : https://prove2.me/theorems/1ababc30-446e-4978-b1a3-ebcfc5e8cc44
-- title:
--   `BookProof.ChapterMackeyInducedSystem.mackey_correspondence` (L : MulAction.stabilizer G x₀ →* (K ≃ₗᵢ[ℂ] K)) (s : X → G) (hs : ∀ x, s x • x₀ = x) (hs0 : s x₀ = 1) : (∀ (a...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMackeyInducedSystem`.
--
--   `BookProof.ChapterMackeyInducedSystem.mackey_correspondence` (L : MulAction.stabilizer G x₀ →* (K ≃ₗᵢ[ℂ] K)) (s : X → G) (hs : ∀ x, s x • x₀ = x) (hs0 : s x₀ = 1) : (∀ (a : MulAction.stabilizer G x₀) (f : FieldSpace X K), ((inducedSystem L s hs).U (a : G) f) x₀ = L a (f x₀)) ∧ (∀ f : FieldSpace X K, (inducedSystem L s hs).p x₀ f = f ↔ ∀ x, x ≠ x₀ → f x = 0) ∧ ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (S : ImprimitivitySystem G X E), (∀ ψ φ : E, mackeyMap S s (ψ + φ) = mackeyMap S s ψ + mackeyMap S s φ) ∧ (∀ ψ : E, ∑ x : X, ‖mackeyMap S s ψ x‖ ^ 2 = ‖ψ‖ ^ 2) ∧ Function.Injective (mackeyMap S s) ∧ (∀ f ∈ InducedSpace S x₀, ∃ ψ : E, mackeyMap S s ψ = f) ∧ (∀ (g : G) (ψ : E), mackeyMap S s (S.U g ψ) = inducedRep S s g (mackeyMap S s ψ)) ∧ (∀ (y : X) (ψ : E), mackeyMap S s (S.p y ψ) = inducedPvm y (mackeyMap S s ψ))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMackeyInducedSystem.mackey_correspondence`.

-- Generated from ChapterMackeyInducedSystem.lean — theorem BookProof.ChapterMackeyInducedSystem.mackey_correspondence
import Mathlib
import Definitions.Def_ChapterMackeyInducedSystem
import Definitions.Def_ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity
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

theorem BookProof.ChapterMackeyInducedSystem.mackey_correspondence (L : MulAction.stabilizer G x₀ →* (K ≃ₗᵢ[ℂ] K)) (s : X → G)
    (hs : ∀ x, s x • x₀ = x) (hs0 : s x₀ = 1) :
    (∀ (a : MulAction.stabilizer G x₀) (f : FieldSpace X K),
        ((inducedSystem L s hs).U (a : G) f) x₀ = L a (f x₀)) ∧
    (∀ f : FieldSpace X K, (inducedSystem L s hs).p x₀ f = f ↔ ∀ x, x ≠ x₀ → f x = 0) ∧
    ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      (S : ImprimitivitySystem G X E),
      (∀ ψ φ : E, mackeyMap S s (ψ + φ) = mackeyMap S s ψ + mackeyMap S s φ) ∧
      (∀ ψ : E, ∑ x : X, ‖mackeyMap S s ψ x‖ ^ 2 = ‖ψ‖ ^ 2) ∧
      Function.Injective (mackeyMap S s) ∧
      (∀ f ∈ InducedSpace S x₀, ∃ ψ : E, mackeyMap S s ψ = f) ∧
      (∀ (g : G) (ψ : E), mackeyMap S s (S.U g ψ) = inducedRep S s g (mackeyMap S s ψ)) ∧
      (∀ (y : X) (ψ : E), mackeyMap S s (S.p y ψ) = inducedPvm y (mackeyMap S s ψ)) := by sorry
