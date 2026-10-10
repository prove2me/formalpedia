-- Prove2me | Theorems.Thm_BookProof_BookBrstYangMills_gaussGenPoly_eq
-- name    : BookProof.BookBrstYangMills.gaussGenPoly_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T13:19:34.638456+00:00
-- url     : https://prove2.me/theorems/6db0a4ef-8b4a-4a1b-a5b2-13ea4a095276
-- title:
--   `BookProof.BookBrstYangMills.gaussGenPoly_eq` (c : Fin N) : gaussGenPoly G c = (-Complex.I) • ((∑ μ, ∑ a, ((G.D μ c a : ℝ) : ℂ) • momPoly μ a) - (∑ μ, ∑ a, ∑ b, ((G.f a b c...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBookBrstYangMills`.
--
--   `BookProof.BookBrstYangMills.gaussGenPoly_eq` (c : Fin N) : gaussGenPoly G c = (-Complex.I) • ((∑ μ, ∑ a, ((G.D μ c a : ℝ) : ℂ) • momPoly μ a) - (∑ μ, ∑ a, ∑ b, ((G.f a b c : ℝ) : ℂ) • (momPoly μ a * AfieldPoly μ b)))
--
--   Formalization note: Lean 4 identifier `BookProof.BookBrstYangMills.gaussGenPoly_eq`.

-- Generated from ChapterBookBrstYangMills.lean — theorem BookProof.BookBrstYangMills.gaussGenPoly_eq
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
import Definitions.Def_ChapterNavierStokesDifferentialL2
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.BookBrstYangMills



open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

theorem BookProof.BookBrstYangMills.gaussGenPoly_eq (c : Fin N) :
    gaussGenPoly G c = (-Complex.I) •
      ((∑ μ, ∑ a, ((G.D μ c a : ℝ) : ℂ) • momPoly μ a)
        - (∑ μ, ∑ a, ∑ b, ((G.f a b c : ℝ) : ℂ) • (momPoly μ a * AfieldPoly μ b))) := by sorry
