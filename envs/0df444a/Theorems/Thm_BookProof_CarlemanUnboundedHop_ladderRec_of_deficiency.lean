-- Prove2me | Theorems.Thm_BookProof_CarlemanUnboundedHop_ladderRec_of_deficiency
-- name    : BookProof.CarlemanUnboundedHop.ladderRec_of_deficiency
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T21:08:46.216011+00:00
-- url     : https://prove2.me/theorems/e69f91b5-9ea1-47ca-bee4-5591b3972e4c
-- title:
--   `BookProof.CarlemanUnboundedHop.ladderRec_of_deficiency` {a : ℕ → ℕ → ℂ} (hk : IsL2Kernel a) {z : ℂ} {w : L2N} (hw : ∀ v : lpFiniteModes ℕ, (inner ℂ (kernelOp hk v) (w : L2N)...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanUnboundedHop`.
--
--   `BookProof.CarlemanUnboundedHop.ladderRec_of_deficiency` {a : ℕ → ℕ → ℂ} (hk : IsL2Kernel a) {z : ℂ} {w : L2N}
--       (hw : ∀ v : lpFiniteModes ℕ, (inner ℂ (kernelOp hk v) (w : L2N) : ℂ)
--           = z * inner ℂ (v : L2N) (w : L2N)) :
--       LadderRecInf a ((w : ℕ → ℂ)) z
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanUnboundedHop.ladderRec_of_deficiency`.

-- Generated from ChapterCarlemanUnboundedHop.lean — theorem BookProof.CarlemanUnboundedHop.ladderRec_of_deficiency
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
import Definitions.Def_ChapterKernelBound
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.KernelBound
open BookProof.NavierStokesFlow.DiagonalEsa
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow.LpNat
open BookProof.CarlemanUnboundedHop



open Finset
open BookProof.NavierStokesFlow

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

theorem BookProof.CarlemanUnboundedHop.ladderRec_of_deficiency {a : ℕ → ℕ → ℂ} (hk : IsL2Kernel a) {z : ℂ} {w : L2N}
    (hw : ∀ v : lpFiniteModes ℕ, (inner ℂ (kernelOp hk v) (w : L2N) : ℂ)
        = z * inner ℂ (v : L2N) (w : L2N)) :
    LadderRecInf a ((w : ℕ → ℂ)) z := by sorry
