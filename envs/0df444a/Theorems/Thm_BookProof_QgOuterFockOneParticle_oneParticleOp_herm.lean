-- Prove2me | Theorems.Thm_BookProof_QgOuterFockOneParticle_oneParticleOp_herm
-- name    : BookProof.QgOuterFockOneParticle.oneParticleOp_herm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:34:17.876846+00:00
-- url     : https://prove2.me/theorems/af957ecb-ca51-4390-911d-dbc4504d4e02
-- title:
--   `BookProof.QgOuterFockOneParticle.oneParticleOp_herm` (a b : ι) (v u : ccDomain ℝ) : (inner ℂ (oneParticleOp W Q b a v) ((u : L2R)) : ℂ) = inner ℂ (v : L2R) (oneParticleOp W Q a b
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockOneParticle`.
--
--   `BookProof.QgOuterFockOneParticle.oneParticleOp_herm` (a b : ι) (v u : ccDomain ℝ) : (inner ℂ (oneParticleOp W Q b a v) ((u : L2R)) : ℂ) = inner ℂ (v : L2R) (oneParticleOp W Q a b u)
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockOneParticle.oneParticleOp_herm`.

-- Generated from ChapterQgOuterFockOneParticle.lean — theorem BookProof.QgOuterFockOneParticle.oneParticleOp_herm
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

theorem BookProof.QgOuterFockOneParticle.oneParticleOp_herm (a b : ι) (v u : ccDomain ℝ) :
    (inner ℂ (oneParticleOp W Q b a v) ((u : L2R)) : ℂ)
      = inner ℂ (v : L2R) (oneParticleOp W Q a b u) := by sorry
