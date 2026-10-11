-- Prove2me | Theorems.Thm_BookProof_ScalaronHermiteEsa_gaussExpDecay_lp
-- name    : BookProof.ScalaronHermiteEsa.gaussExpDecay_lp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T11:42:17.352975+00:00
-- url     : https://prove2.me/theorems/a1f3c8fb-7f21-4217-8fe9-61a880a6604b
-- title:
--   `BookProof.ScalaronHermiteEsa.gaussExpDecay_lp` (w : L2d d) : GaussExpDecay ((w : Vd d → ℂ))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronHermiteEsa`.
--
--   `BookProof.ScalaronHermiteEsa.gaussExpDecay_lp` (w : L2d d) : GaussExpDecay ((w : Vd d → ℂ))
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronHermiteEsa.gaussExpDecay_lp`.

-- Generated from ChapterScalaronHermiteEsa.lean — theorem BookProof.ScalaronHermiteEsa.gaussExpDecay_lp
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

theorem BookProof.ScalaronHermiteEsa.gaussExpDecay_lp (w : L2d d) : GaussExpDecay ((w : Vd d → ℂ)) := by sorry
