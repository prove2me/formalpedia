-- Prove2me | Theorems.Thm_Formalism_HN_place_part_orthogonal
-- name    : Formalism.HN.place_part_orthogonal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:37.307083+00:00
-- url     : https://prove2.me/theorems/3e7646f8-843e-4340-a994-a2db6fc6f64c
-- title:
--   HN: place part orthogonal
-- statement:
--   The HN construction uses the place part orthogonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtImage.lean#L21-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtImage.lean#L21-L32

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN

theorem Formalism.HN.place_part_orthogonal {P ι : Type*} [Fintype P] [Fintype ι] {v w : P} (h : v ≠ w)
    (x : EuclideanSpace ℝ (P × ι × Fin 2)) (hx : x ∈ placePart v)
    (y : EuclideanSpace ℝ (P × ι × Fin 2)) (hy : y ∈ placePart w) : inner ℝ x y = 0 := by sorry
