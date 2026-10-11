-- Prove2me | Theorems.Thm_BookProof_ScalaronHermiteEsa_GaussExpDecay_aestronglyMeasurable
-- name    : BookProof.ScalaronHermiteEsa.GaussExpDecay.aestronglyMeasurable
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T11:41:17.720978+00:00
-- url     : https://prove2.me/theorems/95d55262-f42f-49ea-a662-80942e04f4a3
-- title:
--   `BookProof.ScalaronHermiteEsa.GaussExpDecay.aestronglyMeasurable` {u : Vd d → ℂ} (hu : GaussExpDecay u) : AEStronglyMeasurable u (volume : Measure (Vd d))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalaronHermiteEsa`.
--
--   `BookProof.ScalaronHermiteEsa.GaussExpDecay.aestronglyMeasurable` {u : Vd d → ℂ} (hu : GaussExpDecay u) : AEStronglyMeasurable u (volume : Measure (Vd d))
--
--   Formalization note: Lean 4 identifier `BookProof.ScalaronHermiteEsa.GaussExpDecay.aestronglyMeasurable`.

-- Generated from ChapterScalaronHermiteEsa.lean — theorem BookProof.ScalaronHermiteEsa.GaussExpDecay.aestronglyMeasurable
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

theorem BookProof.ScalaronHermiteEsa.GaussExpDecay.aestronglyMeasurable {u : Vd d → ℂ} (hu : GaussExpDecay u) :
    AEStronglyMeasurable u (volume : Measure (Vd d)) := by sorry
