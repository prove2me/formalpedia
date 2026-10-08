-- Prove2me | Theorems.Thm_BookProof_CarlemanUnboundedHop_kernelOp_stone_flow
-- name    : BookProof.CarlemanUnboundedHop.kernelOp_stone_flow
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:34:45.768987+00:00
-- url     : https://prove2.me/theorems/5fd023ed-f0c4-4864-ad56-5fb687e4b08b
-- title:
--   `BookProof.CarlemanUnboundedHop.kernelOp_stone_flow` {a : ℕ → ℕ → ℂ} {A θ Θ : ℕ → ℝ} (hk : IsL2Kernel a) (hθ0 : ∀ r, 0 ≤ θ r) (hΘ : ∀ j, HasSum (fun i => θ (i + j +...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanUnboundedHop`.
--
--   `BookProof.CarlemanUnboundedHop.kernelOp_stone_flow` {a : ℕ → ℕ → ℂ} {A θ Θ : ℕ → ℝ} (hk : IsL2Kernel a) (hθ0 : ∀ r, 0 ≤ θ r) (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) (hΘsum : Summable Θ) (hApos : ∀ n, 0 < A n) (hAmono : Monotone A) (hbd : ∀ n k, n < k → ‖a n k‖ ≤ A n * θ (k - n)) (hcar : ¬ Summable fun n => (A n)⁻¹) : ∃ (T : ChapterStoneResolvent.UnboundedSelfAdjoint L2N) (U : ℝ → (L2N →L[ℂ] L2N)), EsaClosure.IsSelfAdjointExtension (kernelOp hk) T.op ∧ StoneBridge.IsStoneFlow T U
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanUnboundedHop.kernelOp_stone_flow`.

-- Generated from ChapterCarlemanUnboundedHop.lean — theorem BookProof.CarlemanUnboundedHop.kernelOp_stone_flow
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterKernelBound
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
open BookProof.EsaClosure
open BookProof.KernelBound
open BookProof.NavierStokesFlow.DiagonalEsa
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow.LpNat
open BookProof.StoneBridge
open BookProof.CarlemanUnboundedHop



open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

theorem BookProof.CarlemanUnboundedHop.kernelOp_stone_flow {a : ℕ → ℕ → ℂ} {A θ Θ : ℕ → ℝ} (hk : IsL2Kernel a)
    (hθ0 : ∀ r, 0 ≤ θ r) (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j))
    (hΘsum : Summable Θ) (hApos : ∀ n, 0 < A n) (hAmono : Monotone A)
    (hbd : ∀ n k, n < k → ‖a n k‖ ≤ A n * θ (k - n))
    (hcar : ¬ Summable fun n => (A n)⁻¹) :
    ∃ (T : ChapterStoneResolvent.UnboundedSelfAdjoint L2N) (U : ℝ → (L2N →L[ℂ] L2N)),
      EsaClosure.IsSelfAdjointExtension (kernelOp hk) T.op ∧ StoneBridge.IsStoneFlow T U := by sorry
