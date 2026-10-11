-- Prove2me | Theorems.Thm_BookProof_ScalaronHermiteEsa_moments_of_monomial_moments
-- name    : BookProof.ScalaronHermiteEsa.moments_of_monomial_moments
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T11:42:09.666529+00:00
-- url     : https://prove2.me/theorems/2fcf25d7-b619-4250-90b6-3ae905bc81c4
-- title:
--   `BookProof.ScalaronHermiteEsa.moments_of_monomial_moments` {u : Vd d → ℂ} (hu : GaussExpDecay u) (hmon : ∀ a : Fin d →₀ ℕ, ∫ x : Vd d, pgFun (monomial a (1 : ℂ)) x * u x = 0) (p :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronHermiteEsa`.
--
--   `BookProof.ScalaronHermiteEsa.moments_of_monomial_moments` {u : Vd d → ℂ} (hu : GaussExpDecay u) (hmon : ∀ a : Fin d →₀ ℕ, ∫ x : Vd d, pgFun (monomial a (1 : ℂ)) x * u x = 0) (p : MvPolynomial (Fin d) ℂ) : ∫ x : Vd d, pgFun p x * u x = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronHermiteEsa.moments_of_monomial_moments`.

-- Generated from ChapterScalaronHermiteEsa.lean — theorem BookProof.ScalaronHermiteEsa.moments_of_monomial_moments
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterScalaronHermiteEsa
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteProductCore
open BookProof.ScalaronHermiteEsa



open MeasureTheory Complex MvPolynomial FourierTransform
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine BookProof.Starobinsky
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.ScalaronHermiteEsa.moments_of_monomial_moments {u : Vd d → ℂ} (hu : GaussExpDecay u)
    (hmon : ∀ a : Fin d →₀ ℕ, ∫ x : Vd d, pgFun (monomial a (1 : ℂ)) x * u x = 0)
    (p : MvPolynomial (Fin d) ℂ) : ∫ x : Vd d, pgFun p x * u x = 0 := by sorry
