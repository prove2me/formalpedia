-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_GeneralGermZero_sysK_P
-- name    : Formalism.L2.FormalSeriesBounds.GeneralGermZero.sysK_P
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:03:12.349045+00:00
-- url     : https://prove2.me/theorems/aed3b5f2-4048-4e4f-a60d-6bb9a33014a4
-- title:
--   General Germ Zero: sys K P
-- statement:
--   The General Germ Zero construction uses the sys K P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeneralGermZero.lean#L120-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GeneralGermZero.lean#L120-L210

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffSingleSubstOfLowDegree
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeneralGermZero
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

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
open Formalism.L2.FormalSeriesBounds.GeneralGermZero
open Formalism.IncomingBounds FormalGermZero
variable {C : Type} [Field C] {κ : Type} [Fintype κ]
variable {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (X : RawChart C d I κ)
  (F : κ → MvPowerSeries (Fin 2 × κ) C) (hF0 : ∀ k, MvPowerSeries.constantCoeff (F k) = 0)
  (hFI : ∀ k, IntS V (F k)) (hadd : LgAdd F X.lg)
  (hlin : ∀ k (μ : κ →₀ ℕ), μ.degree ≤ 1 → MvPowerSeries.coeff μ (X.lg k) = MvPowerSeries.coeff μ (MvPowerSeries.X k))
  (hexlg : ∀ k, MvPowerSeries.subst X.lg (X.ex k) = (MvPowerSeries.X k : MvPowerSeries κ C))
include hF0 hFI hadd hlin hexlg

theorem Formalism.L2.FormalSeriesBounds.GeneralGermZero.sysK_P {g : Fin 2} (hg : X.CartHyp V g) (S : Sys (RawChart.cart hg)) :
    ∃ P : κ → MvPowerSeries (I g) C, (∀ j, MvPowerSeries.constantCoeff (P j) = 0) ∧
      (∀ j, IntS V (P j)) ∧
      (∀ j c, MvPowerSeries.coeff (Finsupp.single c 1) (P j) = ∑ c', X.u g c' j * S.tan c c') ∧
      ∀ t : I g → MvPowerSeries (I g) C, S.IsT t → ∀ j,
        MvPowerSeries.subst t (P j) =
          MvPowerSeries.subst (fun i => ∑ c', X.u g c' i • (MvPowerSeries.X c' : MvPowerSeries (I g) C)) (X.ex j) := by sorry
