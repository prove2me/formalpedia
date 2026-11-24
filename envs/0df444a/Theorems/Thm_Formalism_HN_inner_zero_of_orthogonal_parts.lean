-- Prove2me | Theorems.Thm_Formalism_HN_inner_zero_of_orthogonal_parts
-- name    : Formalism.HN.inner_zero_of_orthogonal_parts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:33.108613+00:00
-- url     : https://prove2.me/theorems/59c7d04a-49d3-4445-afb5-479818d508db
-- title:
--   HN: inner zero of orthogonal parts
-- statement:
--   The HN construction uses the inner zero of orthogonal parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtImage.lean#L51-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtImage.lean#L51-L65

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

theorem Formalism.HN.inner_zero_of_orthogonal_parts {P E : Type*} [Fintype P] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (Ev : P → Submodule ℝ E) (hEv : ∀ v w, v ≠ w → ∀ x ∈ Ev v, ∀ y ∈ Ev w, inner ℝ x y = 0)
    (T : Submodule ℝ E) (hT : T = ⨆ v, T ⊓ Ev v) {v : P} {x : E} (hxv : x ∈ Ev v)
    (hx : ∀ t ∈ T ⊓ Ev v, inner ℝ t x = 0) : ∀ t ∈ T, inner ℝ t x = 0 := by sorry
