-- Prove2me | Theorems.Thm_BookProof_BookBrstYangMills_I_smul_gaussGen
-- name    : BookProof.BookBrstYangMills.I_smul_gaussGen
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:20:22.072228+00:00
-- url     : https://prove2.me/theorems/c97765cb-6427-4df5-8bf0-5237c28debca
-- title:
--   `BookProof.BookBrstYangMills.I_smul_gaussGen` (c : Fin N) : Complex.I • gaussGen G c = (∑ μ, ∑ a, ((G.D μ c a : ℝ) : ℂ) • mom μ a) - (∑ μ, ∑ a, ∑ b, ((G.f a b c : ℝ) :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBookBrstYangMills`.
--
--   `BookProof.BookBrstYangMills.I_smul_gaussGen` (c : Fin N) : Complex.I • gaussGen G c = (∑ μ, ∑ a, ((G.D μ c a : ℝ) : ℂ) • mom μ a) - (∑ μ, ∑ a, ∑ b, ((G.f a b c : ℝ) : ℂ) • (mom μ a * Afield μ b))
--
--   Formalization note: Lean 4 identifier `BookProof.BookBrstYangMills.I_smul_gaussGen`.

-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.I_smul_gaussGen
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterYangMillsGhostSector
open BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.YangMillsGhost
open BookProof.BookBrstYangMills



open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

theorem BookProof.BookBrstYangMills.I_smul_gaussGen (c : Fin N) :
    Complex.I • gaussGen G c
      = (∑ μ, ∑ a, ((G.D μ c a : ℝ) : ℂ) • mom μ a)
        - (∑ μ, ∑ a, ∑ b, ((G.f a b c : ℝ) : ℂ) • (mom μ a * Afield μ b)) := by sorry
