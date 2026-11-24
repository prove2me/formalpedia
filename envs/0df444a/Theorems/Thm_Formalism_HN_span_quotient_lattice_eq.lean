-- Prove2me | Theorems.Thm_Formalism_HN_span_quotient_lattice_eq
-- name    : Formalism.HN.span_quotient_lattice_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:30:02.596303+00:00
-- url     : https://prove2.me/theorems/e1a19a12-dcf1-432c-b52e-bae0a16e97d4
-- title:
--   HN: span quotient lattice eq
-- statement:
--   The HN construction uses the span quotient lattice eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtImage.lean#L113-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtImage.lean#L113-L137

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

theorem Formalism.HN.span_quotient_lattice_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (L N : Submodule ℤ E) (h : N ≤ L) :
    Submodule.span ℝ (Formalism.F.quot L N : Set E) =
      Submodule.span ℝ (L : Set E) ⊓ (Submodule.span ℝ (N : Set E))ᗮ := by sorry
