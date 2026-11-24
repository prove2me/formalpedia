-- Prove2me | Theorems.Thm_Formalism_HN_orthogonal_complement_place_split
-- name    : Formalism.HN.orthogonal_complement_place_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:29.367803+00:00
-- url     : https://prove2.me/theorems/dcb0396a-8ccb-49c8-9e03-c511e9a087c5
-- title:
--   HN: orthogonal complement place split
-- statement:
--   The HN construction uses the orthogonal complement place split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtImage.lean#L67-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtImage.lean#L67-L111

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

theorem Formalism.HN.orthogonal_complement_place_split {P E : Type*} [Fintype P] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Ev : P → Submodule ℝ E) (hEv : ∀ v w, v ≠ w → ∀ x ∈ Ev v, ∀ y ∈ Ev w, inner ℝ x y = 0)
    (S T : Submodule ℝ E) (hS : S = ⨆ v, S ⊓ Ev v) (hT : T = ⨆ v, T ⊓ Ev v) (hTS : T ≤ S) :
    S ⊓ Tᗮ = (⨆ v, S ⊓ Tᗮ ⊓ Ev v) ∧
    ∀ v, finrank ℝ (S ⊓ Tᗮ ⊓ Ev v : Submodule ℝ E) + finrank ℝ (T ⊓ Ev v : Submodule ℝ E) =
      finrank ℝ (S ⊓ Ev v : Submodule ℝ E) := by sorry
