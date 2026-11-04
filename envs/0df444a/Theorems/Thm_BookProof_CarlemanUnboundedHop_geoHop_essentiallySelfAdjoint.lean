-- Prove2me | Theorems.Thm_BookProof_CarlemanUnboundedHop_geoHop_essentiallySelfAdjoint
-- name    : BookProof.CarlemanUnboundedHop.geoHop_essentiallySelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T14:41:17.048872+00:00
-- url     : https://prove2.me/theorems/20df3aa5-d5e9-4a37-bd8e-c0dce7043966
-- title:
--   `BookProof.CarlemanUnboundedHop.geoHop_essentiallySelfAdjoint` (b : ℕ → ℝ) {rho : ℝ} (hrho : 0 ≤ rho) (hrho1 : rho < 1) : EssentiallySelfAdjointOn (lpFiniteModes ℕ) (kernelOp...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanUnboundedHop`.
--
--   `BookProof.CarlemanUnboundedHop.geoHop_essentiallySelfAdjoint` (b : ℕ → ℝ) {rho : ℝ} (hrho : 0 ≤ rho) (hrho1 : rho < 1) :
--       EssentiallySelfAdjointOn (lpFiniteModes ℕ) (kernelOp (geoHop_isL2Kernel b hrho hrho1))
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanUnboundedHop.geoHop_essentiallySelfAdjoint`.

-- Generated from ChapterCarlemanUnboundedHop.lean — theorem BookProof.CarlemanUnboundedHop.geoHop_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterKernelBound
import Definitions.Def_ChapterNavierStokesEsa
import Theorems.Thm_BookProof_CarlemanUnboundedHop_geoHop_isL2Kernel
open BookProof.KernelBound
open BookProof.CarlemanUnboundedHop



open Finset
open BookProof.FarisLavine
open BookProof.NavierStokesFlow

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

theorem BookProof.CarlemanUnboundedHop.geoHop_essentiallySelfAdjoint (b : ℕ → ℝ) {rho : ℝ} (hrho : 0 ≤ rho)
    (hrho1 : rho < 1) :
    EssentiallySelfAdjointOn (lpFiniteModes ℕ) (kernelOp (geoHop_isL2Kernel b hrho hrho1)) := by sorry
