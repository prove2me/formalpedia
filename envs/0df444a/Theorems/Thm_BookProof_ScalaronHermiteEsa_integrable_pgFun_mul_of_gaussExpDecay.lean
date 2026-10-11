-- Prove2me | Theorems.Thm_BookProof_ScalaronHermiteEsa_integrable_pgFun_mul_of_gaussExpDecay
-- name    : BookProof.ScalaronHermiteEsa.integrable_pgFun_mul_of_gaussExpDecay
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T11:41:25.484507+00:00
-- url     : https://prove2.me/theorems/41728a47-51be-48dc-901e-716ddb3d244d
-- title:
--   `BookProof.ScalaronHermiteEsa.integrable_pgFun_mul_of_gaussExpDecay` {u : Vd d → ℂ} (hu : GaussExpDecay u) (p : MvPolynomial (Fin d) ℂ) : Integrable (fun x : Vd d => pgFun p x * u
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronHermiteEsa`.
--
--   `BookProof.ScalaronHermiteEsa.integrable_pgFun_mul_of_gaussExpDecay` {u : Vd d → ℂ} (hu : GaussExpDecay u) (p : MvPolynomial (Fin d) ℂ) : Integrable (fun x : Vd d => pgFun p x * u x)
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronHermiteEsa.integrable_pgFun_mul_of_gaussExpDecay`.

-- Generated from ChapterScalaronHermiteEsa.lean — theorem BookProof.ScalaronHermiteEsa.integrable_pgFun_mul_of_gaussExpDecay
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

theorem BookProof.ScalaronHermiteEsa.integrable_pgFun_mul_of_gaussExpDecay {u : Vd d → ℂ} (hu : GaussExpDecay u)
    (p : MvPolynomial (Fin d) ℂ) : Integrable (fun x : Vd d => pgFun p x * u x) := by sorry
