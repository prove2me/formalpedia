-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_commutesWithContMult_conjRepSymm
-- name    : BookProof.ChapterAbelianCyclicCommutant.commutesWithContMult_conjRepSymm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:49:40.296151+00:00
-- url     : https://prove2.me/theorems/5abe6eaa-16f3-4927-8d4a-3ce9b9bbe19f
-- title:
--   `BookProof.ChapterAbelianCyclicCommutant.commutesWithContMult_conjRepSymm` {S : H →L[ℂ] H} (hS : ∀ g : C(X, ℂ), pi g * S = S * pi g) : CommutesWithContMult (conjRepSymm pi xi hcyc
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianCyclicCommutant`.
--
--   `BookProof.ChapterAbelianCyclicCommutant.commutesWithContMult_conjRepSymm` {S : H →L[ℂ] H} (hS : ∀ g : C(X, ℂ), pi g * S = S * pi g) : CommutesWithContMult (conjRepSymm pi xi hcyc S)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianCyclicCommutant.commutesWithContMult_conjRepSymm`.

-- Generated from ChapterAbelianCyclicCommutant.lean — theorem BookProof.ChapterAbelianCyclicCommutant.commutesWithContMult_conjRepSymm
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterLinftyMaximalAbelian
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterSpectralCommutant
import Definitions.Def_ChapterAbelianCyclicModel
import Mathlib
import Definitions.Def_ChapterAbelianCyclicCommutant
open BookProof.ChapterAbelianCyclicCommutant


noncomputable section

open MeasureTheory Complex WeakDual


open BookProof.ChapterLinftyMultiplication BookProof.ChapterLinftyMaximalAbelian
open BookProof.ChapterAbelianGelfandModel BookProof.ChapterSpectralCommutant
open BookProof.ChapterAbelianCyclicModel


variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (pi : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H) (hcyc : DenseRange (repVec pi xi))

theorem BookProof.ChapterAbelianCyclicCommutant.commutesWithContMult_conjRepSymm {S : H →L[ℂ] H}
    (hS : ∀ g : C(X, ℂ), pi g * S = S * pi g) :
    CommutesWithContMult (conjRepSymm pi xi hcyc S) := by sorry
