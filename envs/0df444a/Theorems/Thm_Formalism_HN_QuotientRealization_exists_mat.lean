-- Prove2me | Theorems.Thm_Formalism_HN_QuotientRealization_exists_mat
-- name    : Formalism.HN.QuotientRealization.exists_mat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:15.052773+00:00
-- url     : https://prove2.me/theorems/e661ec95-1747-40f2-8ff4-0a857661eea4
-- title:
--   Quotient Realization: exists mat
-- statement:
--   The Quotient Realization construction uses the exists mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/QuotRealize.lean#L132-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/QuotRealize.lean#L132-L159

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

theorem Formalism.HN.QuotientRealization.exists_mat {κ ι : Type} [Fintype κ] [DecidableEq κ] [Fintype ι]
    (T : (κ → ℂ) →ₗ[ℂ] EuclideanSpace ℂ ι) (hT : Function.Injective T) :
    ∃ M : Matrix κ κ ℂ, IsUnit M.det ∧ ∀ z, Formalism.HermitianLatticesTheory.cnorm (M *ᵥ z) = ‖T z‖ := by sorry
