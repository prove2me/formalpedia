-- Prove2me | Theorems.Thm_Formalism_HN_QuotientRealization_transport_apply
-- name    : Formalism.HN.QuotientRealization.transport_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:29.032724+00:00
-- url     : https://prove2.me/theorems/c2739709-a9d2-49c8-9442-04a2189e71bf
-- title:
--   Quotient Realization: transport apply
-- statement:
--   The Quotient Realization construction uses the transport apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/QuotRealize.lean#L45-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/QuotRealize.lean#L45-L50

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_QuotRealize
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
open Formalism.HN.QuotientRealization
variable {E F M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [AddCommGroup M]

theorem Formalism.HN.QuotientRealization.transport_apply (f : M →+ E) (g : M →+ F) (L1 : Submodule ℤ E) (L2 : Submodule ℤ F)
    (h1 : ∀ y, y ∈ L1 ↔ ∃ m, f m = y) (h2 : ∀ y, y ∈ L2 ↔ ∃ m, g m = y)
    (hn : ∀ m, ‖f m‖ = ‖g m‖) (y : L1) (m : M) (hm : f m = y) :
    ((transport f g L1 L2 h1 h2 hn y : L2) : F) = g m := by sorry
