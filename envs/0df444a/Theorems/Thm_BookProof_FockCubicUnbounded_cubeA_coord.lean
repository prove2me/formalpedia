-- Prove2me | Theorems.Thm_BookProof_FockCubicUnbounded_cubeA_coord
-- name    : BookProof.FockCubicUnbounded.cubeA_coord
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:33:47.937992+00:00
-- url     : https://prove2.me/theorems/e8ee7f23-2398-4d18-bbb9-7ea3c9168e95
-- title:
--   `BookProof.FockCubicUnbounded.cubeA_coord` (k : ℕ) (x : FockAlg) (γ : Conf) : cubeA k x γ = ((Real.sqrt (γ k) : ℝ) : ℂ) * ((Real.sqrt ((dn k γ) k) : ℝ) : ℂ) * ((Real.sqrt ((dn k (d
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockCubicUnbounded`.
--
--   `BookProof.FockCubicUnbounded.cubeA_coord` (k : ℕ) (x : FockAlg) (γ : Conf) : cubeA k x γ = ((Real.sqrt (γ k) : ℝ) : ℂ) * ((Real.sqrt ((dn k γ) k) : ℝ) : ℂ) * ((Real.sqrt ((dn k (dn k γ)) k) : ℝ) : ℂ) * x (dn k (dn k (dn k γ))) + ((Real.sqrt ((γ k : ℝ) + 1) : ℝ) : ℂ) * ((Real.sqrt (((up k γ) k : ℝ) + 1) : ℝ) : ℂ) * ((Real.sqrt (((up k (up k γ)) k : ℝ) + 1) : ℝ) : ℂ) * x (up k (up k (up k γ)))
--
--   Formalization note: Lean 4 identifier `BookProof.FockCubicUnbounded.cubeA_coord`.

-- Generated from ChapterFockCubicUnbounded.lean — theorem BookProof.FockCubicUnbounded.cubeA_coord
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockFieldPerturbation
import Mathlib
import Definitions.Def_ChapterFockCubicUnbounded
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization
open BookProof.FockCubicUnbounded


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation

theorem BookProof.FockCubicUnbounded.cubeA_coord (k : ℕ) (x : FockAlg) (γ : Conf) :
    cubeA k x γ
      = ((Real.sqrt (γ k) : ℝ) : ℂ) * ((Real.sqrt ((dn k γ) k) : ℝ) : ℂ)
          * ((Real.sqrt ((dn k (dn k γ)) k) : ℝ) : ℂ) * x (dn k (dn k (dn k γ)))
        + ((Real.sqrt ((γ k : ℝ) + 1) : ℝ) : ℂ)
            * ((Real.sqrt (((up k γ) k : ℝ) + 1) : ℝ) : ℂ)
            * ((Real.sqrt (((up k (up k γ)) k : ℝ) + 1) : ℝ) : ℂ)
            * x (up k (up k (up k γ))) := by sorry
