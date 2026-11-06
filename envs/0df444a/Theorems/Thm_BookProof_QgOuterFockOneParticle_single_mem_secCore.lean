-- Prove2me | Theorems.Thm_BookProof_QgOuterFockOneParticle_single_mem_secCore
-- name    : BookProof.QgOuterFockOneParticle.single_mem_secCore
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-05T13:11:26.15087+00:00
-- url     : https://prove2.me/theorems/af6c38ef-dc47-48bb-a5e1-cb629a5f3e4b
-- title:
--   `BookProof.QgOuterFockOneParticle.single_mem_secCore` (b : ι) (u : ccDomain ℝ) : (lp.single 2 b ((u : L2R)) : Sec ι) ∈ secCore (ι
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgOuterFockOneParticle`.
--
--   `BookProof.QgOuterFockOneParticle.single_mem_secCore` (b : ι) (u : ccDomain ℝ) : (lp.single 2 b ((u : L2R)) : Sec ι) ∈ secCore (ι
--
--   Formalization note: Lean 4 identifier `BookProof.QgOuterFockOneParticle.single_mem_secCore`.

-- Generated from ChapterQgOuterFockOneParticle.lean — theorem BookProof.QgOuterFockOneParticle.single_mem_secCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterScalaronOuterFockFL
import Mathlib
import Definitions.Def_ChapterQgOuterFockOneParticle
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronFiberFL
open BookProof.ScalaronEsa
open BookProof.ScalaronFiberFL
open BookProof.ScalaronFiberFL.WallPot
open BookProof.QgOuterFockOneParticle



open MeasureTheory
open BookProof.FarisLavine BookProof.ScalaronEsa
open BookProof.DirectSumEsa BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL

noncomputable section

variable {ι : Type*} [DecidableEq ι] (W : WallPot) (Q : QgModeData ι)

theorem BookProof.QgOuterFockOneParticle.single_mem_secCore (b : ι) (u : ccDomain ℝ) :
    (lp.single 2 b ((u : L2R)) : Sec ι) ∈ secCore (ι := ι) := by sorry
