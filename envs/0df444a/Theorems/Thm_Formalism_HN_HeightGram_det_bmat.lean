-- Prove2me | Theorems.Thm_Formalism_HN_HeightGram_det_bmat
-- name    : Formalism.HN.HeightGram.det_bmat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:01.113752+00:00
-- url     : https://prove2.me/theorems/49cf206c-d178-40a5-b8ba-d8258b9292f7
-- title:
--   Height Gram: det bmat
-- statement:
--   The Height Gram construction uses the det bmat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtGram.lean#L150-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtGram.lean#L150-L163

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
variable {P S : Type} [Fintype P] [DecidableEq P] [Fintype S] [DecidableEq S] {j : ℕ}

theorem Formalism.HN.HeightGram.det_bmat (G : P → Matrix (Fin j) (Fin j) ℂ) :
    (bmat G).det = ∏ v, Complex.normSq (G v).det := by sorry
