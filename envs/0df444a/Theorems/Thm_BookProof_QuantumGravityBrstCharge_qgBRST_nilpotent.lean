-- Prove2me | Theorems.Thm_BookProof_QuantumGravityBrstCharge_qgBRST_nilpotent
-- name    : BookProof.QuantumGravityBrstCharge.qgBRST_nilpotent
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T22:57:43.627006+00:00
-- url     : https://prove2.me/theorems/6e172966-8cb4-44bb-b7f0-72f4a14022c3
-- title:
--   `BookProof.QuantumGravityBrstCharge.qgBRST_nilpotent` (M : Fin 19 → Matrix (Fin 84) (Fin 84) ℝ) (f : Fin 19 → Fin 19 → Fin 19 → ℝ) (hclose : ∀ a b, M a * M b - M b * M a = ∑ e, f a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityBrstCharge`.
--
--   `BookProof.QuantumGravityBrstCharge.qgBRST_nilpotent` (M : Fin 19 → Matrix (Fin 84) (Fin 84) ℝ) (f : Fin 19 → Fin 19 → Fin 19 → ℝ) (hclose : ∀ a b, M a * M b - M b * M a = ∑ e, f a b e • M e) (hf12 : ∀ a b c, f a b c = -f b a c) (hjac : ∀ a b c h : Fin 19, ∑ e, (f a b e * f e c h + f b c e * f e a h + f c a e * f e b h) = 0) : qgBRST M f * qgBRST M f = 0
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityBrstCharge.qgBRST_nilpotent`.

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.qgBRST_nilpotent
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterQuantumGravity3DGauge
import Mathlib
import Definitions.Def_ChapterQuantumGravityBrstCharge
open BookProof.QuantumGravityBrstCharge



open MvPolynomial BookProof.BRSTNilpotent BookProof.YangMillsHermite
open BookProof.QuantumGravity3DGauge

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {f : Fin n → Fin n → Fin n → ℝ} {G χ β : Fin n → R}
variable {d : ℕ}
variable {α : Type*}

theorem BookProof.QuantumGravityBrstCharge.qgBRST_nilpotent (M : Fin 19 → Matrix (Fin 84) (Fin 84) ℝ)
    (f : Fin 19 → Fin 19 → Fin 19 → ℝ)
    (hclose : ∀ a b, M a * M b - M b * M a = ∑ e, f a b e • M e)
    (hf12 : ∀ a b c, f a b c = -f b a c)
    (hjac : ∀ a b c h : Fin 19,
      ∑ e, (f a b e * f e c h + f b c e * f e a h + f c a e * f e b h) = 0) :
    qgBRST M f * qgBRST M f = 0 := by sorry
