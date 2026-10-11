-- Prove2me | Theorems.Thm_BookProof_TensorPerm_permOp_succ
-- name    : BookProof.TensorPerm.permOp_succ
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:05:23.598212+00:00
-- url     : https://prove2.me/theorems/032a9ee9-c80a-4221-a266-6cf48ea02d95
-- title:
--   `BookProof.TensorPerm.permOp_succ` (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) : permOp E (n + 1) σ = (swap0 E (n + 1) (Equiv.Perm.decomposeFin σ).1).trans (liftTail E (permOp E n (Equi
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTensorPermutation`.
--
--   `BookProof.TensorPerm.permOp_succ` (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) : permOp E (n + 1) σ = (swap0 E (n + 1) (Equiv.Perm.decomposeFin σ).1).trans (liftTail E (permOp E n (Equiv.Perm.decomposeFin σ).2))
--
--   Formalization note: Lean 4 identifier `BookProof.TensorPerm.permOp_succ`.

-- Generated from ChapterTensorPermutation.lean — theorem BookProof.TensorPerm.permOp_succ
import Definitions.Def_ChapterGroupAverageEsa
import Mathlib
import Definitions.Def_ChapterTensorPermutation
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterTensorGraphCore
open BookProof.ChapterGaugeUnconstrainedSpectrum
open BookProof.TensorCore
open BookProof.TensorPerm



open scoped TensorProduct
open BookProof.TensorCore BookProof.GroupAverage

noncomputable section

variable (E : BookProof.TensorCore.IPSpace)

theorem BookProof.TensorPerm.permOp_succ (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    permOp E (n + 1) σ = (swap0 E (n + 1) (Equiv.Perm.decomposeFin σ).1).trans
      (liftTail E (permOp E n (Equiv.Perm.decomposeFin σ).2)) := by sorry
