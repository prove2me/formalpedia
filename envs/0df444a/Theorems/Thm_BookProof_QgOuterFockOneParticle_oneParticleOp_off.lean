-- Prove2me | Theorems.Thm_BookProof_QgOuterFockOneParticle_oneParticleOp_off
-- name    : BookProof.QgOuterFockOneParticle.oneParticleOp_off
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:32:43.392111+00:00
-- url     : https://prove2.me/theorems/f9750bf5-3b15-4452-8131-a8a1a80ec228
-- title:
--   `BookProof.QgOuterFockOneParticle.oneParticleOp_off` {a b : ι} (hab : a ≠ b) (hb : b ∉ Q.nbr a) : oneParticleOp W Q a b = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockOneParticle`.
--
--   `BookProof.QgOuterFockOneParticle.oneParticleOp_off` {a b : ι} (hab : a ≠ b) (hb : b ∉ Q.nbr a) : oneParticleOp W Q a b = 0
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockOneParticle.oneParticleOp_off`.

-- Generated from ChapterQgOuterFockOneParticle.lean — theorem BookProof.QgOuterFockOneParticle.oneParticleOp_off
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Mathlib
import Definitions.Def_ChapterQgOuterFockOneParticle
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterQgOuterFockFlow
open BookProof.ScalaronEsa



open MeasureTheory
open BookProof.FarisLavine BookProof.ScalaronEsa
open BookProof.DirectSumEsa BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL

noncomputable section

variable {ι : Type*} [DecidableEq ι] (W : WallPot) (Q : QgModeData ι)

theorem BookProof.QgOuterFockOneParticle.oneParticleOp_off {a b : ι} (hab : a ≠ b) (hb : b ∉ Q.nbr a) :
    oneParticleOp W Q a b = 0 := by sorry
