-- Prove2me | Theorems.Thm_Formalism_HN_HeightGram_det_realif
-- name    : Formalism.HN.HeightGram.det_realif
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:04.067889+00:00
-- url     : https://prove2.me/theorems/0bd037a9-a93c-492d-8d08-3b2ffa55dd28
-- title:
--   Height Gram: det realif
-- statement:
--   The Height Gram construction uses the det realif property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtGram.lean#L89-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtGram.lean#L89-L131

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.HeightGram
variable {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.HN.HeightGram.det_realif (G : Matrix n n ℂ) : (realif G).det = Complex.normSq G.det := by sorry
