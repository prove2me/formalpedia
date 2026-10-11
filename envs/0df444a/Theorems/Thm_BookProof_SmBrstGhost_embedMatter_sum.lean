-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_embedMatter_sum
-- name    : BookProof.SmBrstGhost.embedMatter_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:25:53.687422+00:00
-- url     : https://prove2.me/theorems/7287064e-aa85-4a90-85bb-eaa33081ffe7
-- title:
--   `BookProof.SmBrstGhost.embedMatter_sum` {m : ℕ} {ι : Type*} (s : Finset ι) (M : ι → Matrix (Fin m) (Fin m) ℂ) : embedMatter m (∑ t ∈ s, M t) = ∑ t ∈ s, embedMatter m (M t)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.embedMatter_sum` {m : ℕ} {ι : Type*} (s : Finset ι) (M : ι → Matrix (Fin m) (Fin m) ℂ) : embedMatter m (∑ t ∈ s, M t) = ∑ t ∈ s, embedMatter m (M t)
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.embedMatter_sum`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.embedMatter_sum
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
open BookProof.SmBrstGhost



open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

variable {m : ℕ}
variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {N : ℕ}

theorem BookProof.SmBrstGhost.embedMatter_sum {m : ℕ} {ι : Type*} (s : Finset ι) (M : ι → Matrix (Fin m) (Fin m) ℂ) :
    embedMatter m (∑ t ∈ s, M t) = ∑ t ∈ s, embedMatter m (M t) := by sorry
