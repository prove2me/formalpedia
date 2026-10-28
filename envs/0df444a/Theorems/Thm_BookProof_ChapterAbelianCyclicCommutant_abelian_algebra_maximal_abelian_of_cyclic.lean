-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianCyclicCommutant_abelian_algebra_maximal_abelian_of_cyclic
-- name    : BookProof.ChapterAbelianCyclicCommutant.abelian_algebra_maximal_abelian_of_cyclic
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:49:56.918235+00:00
-- url     : https://prove2.me/theorems/cbb2620e-7730-44b1-bf01-06d52efa6049
-- title:
--   `BookProof.ChapterAbelianCyclicCommutant.abelian_algebra_maximal_abelian_of_cyclic` (rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H) (hcyc : DenseRange fun a : A => rho a xi) : (Set.range fun
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianCyclicCommutant`.
--
--   `BookProof.ChapterAbelianCyclicCommutant.abelian_algebra_maximal_abelian_of_cyclic` (rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H) (hcyc : DenseRange fun a : A => rho a xi) : (Set.range fun a : A => rho a).centralizer.centralizer = (Set.range fun a : A => rho a).centralizer ∧ ∀ S R : H →L[ℂ] H, S ∈ (Set.range fun a : A => rho a).centralizer → R ∈ (Set.range fun a : A => rho a).centralizer → S * R = R * S
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianCyclicCommutant.abelian_algebra_maximal_abelian_of_cyclic`.

-- Generated from ChapterAbelianCyclicCommutant.lean — theorem BookProof.ChapterAbelianCyclicCommutant.abelian_algebra_maximal_abelian_of_cyclic
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

variable {A : Type*} [CommCStarAlgebra A]

theorem BookProof.ChapterAbelianCyclicCommutant.abelian_algebra_maximal_abelian_of_cyclic (rho : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (xi : H)
    (hcyc : DenseRange fun a : A => rho a xi) :
    (Set.range fun a : A => rho a).centralizer.centralizer
        = (Set.range fun a : A => rho a).centralizer ∧
      ∀ S R : H →L[ℂ] H, S ∈ (Set.range fun a : A => rho a).centralizer →
        R ∈ (Set.range fun a : A => rho a).centralizer → S * R = R * S := by sorry
