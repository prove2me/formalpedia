-- Prove2me | Theorems.Thm_Formalism_HN_Rerealization_transfer
-- name    : Formalism.HN.Rerealization.transfer
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:57.00481+00:00
-- url     : https://prove2.me/theorems/ffdcf58f-2180-4509-95b0-9d52ae44a3c1
-- title:
--   Rerealization: transfer
-- statement:
--   The Rerealization construction uses the transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Rerealize.lean#L143-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Rerealize.lean#L143-L190

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
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
open Formalism.HN.Rerealization
variable {R V E E₂ : Type*} [Ring R] [AddCommGroup V] [Module R V] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup E₂]
  [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]

theorem Formalism.HN.Rerealization.transfer (ρ : V →+ E) (ρ₂ : V →+ E₂) (hn : ∀ x, ‖ρ₂ x‖ = ‖ρ x‖) (L : Submodule R V)
    (hL : IsLat ρ L) (hL₂ : IsLat ρ₂ L) :
    (∀ N : Submodule R V, N ≤ L → Formalism.F.covol (zl ρ₂ N) = Formalism.F.covol (zl ρ N) ∧
      rk ρ₂ N = rk ρ N ∧ deg ρ₂ N = deg ρ N ∧ slope ρ₂ N = slope ρ N) ∧
    (∀ N : Submodule R V, IsSat ρ₂ L N ↔ IsSat ρ L N) ∧
    (∀ N : Submodule R V, IsSat ρ L N →
      Formalism.F.covol (Formalism.F.quot (zl ρ₂ L) (zl ρ₂ N)) = Formalism.F.covol (Formalism.F.quot (zl ρ L) (zl ρ N)) ∧
      Formalism.F.slope (Formalism.F.quot (zl ρ₂ L) (zl ρ₂ N)) =
        Formalism.F.slope (Formalism.F.quot (zl ρ L) (zl ρ N))) := by sorry
