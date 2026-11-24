-- Prove2me | Theorems.Thm_Formalism_HN_HeightGram_det_gmat
-- name    : Formalism.HN.HeightGram.det_gmat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:44.284782+00:00
-- url     : https://prove2.me/theorems/cf44fdea-e3be-4ba1-bc50-a5c05bda1776
-- title:
--   Height Gram: det gmat
-- statement:
--   The Height Gram construction uses the det gmat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtGram.lean#L191-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtGram.lean#L191-L197

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

theorem Formalism.HN.HeightGram.det_gmat (lam : P → S → ℂ) (G : P → Matrix (Fin j) (Fin j) ℂ) (eS : S ≃ P × Fin 2) :
    (gmat lam G).det = (amat lam eS).det ^ (2 * j) * ∏ v, Complex.normSq (G v).det := by sorry
