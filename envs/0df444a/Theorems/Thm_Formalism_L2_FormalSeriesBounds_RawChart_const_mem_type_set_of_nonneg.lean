-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_const_mem_type_set_of_nonneg
-- name    : Formalism.L2.FormalSeriesBounds.RawChart.const_mem_type_set_of_nonneg
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:30:55.826781+00:00
-- url     : https://prove2.me/theorems/6c393042-bcea-47c6-9a73-bd3176cb8c8c
-- title:
--   Raw Chart: const mem type set of nonneg
-- statement:
--   The Raw Chart construction uses the const mem type set of nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstMemTypeSetOfNonneg.lean#L249-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstMemTypeSetOfNonneg.lean#L249-L289

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstMemTypeSetOfNonneg
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
open Formalism.L2.FormalSeriesBounds.RawChart
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

theorem Formalism.L2.FormalSeriesBounds.RawChart.const_mem_type_set_of_nonneg (hlg : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 0) → MvPowerSeries.coeff e X.h = 0)
    (V : VF C) (g : Fin 2) (ζ : JJ I g → C) (hζ : ∀ q, V.Ge 0 (ζ q)) :
    const0 (Sum.elim 0 ζ) ∈ X.TySet V g := by sorry
