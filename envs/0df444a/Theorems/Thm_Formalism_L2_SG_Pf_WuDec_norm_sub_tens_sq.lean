-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_WuDec_norm_sub_tens_sq
-- name    : Formalism.L2.SG.Pf.WuDec.norm_sub_tens_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:43.054219+00:00
-- url     : https://prove2.me/theorems/f9e01b2b-ea32-4168-908d-bf17dc35ddea
-- title:
--   Wu Dec: norm sub tens sq
-- statement:
--   The Wu Dec construction uses the norm sub tens sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/TensInt.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/TensInt.lean#L25-L31

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_TensInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.WuDec
variable {ι : Type} [Fintype ι] {V : ι → Type} [∀ v, NormedAddCommGroup (V v)] [∀ v, InnerProductSpace ℂ (V v)]
  {Vπ : Type} [NormedAddCommGroup Vπ] [InnerProductSpace ℂ Vπ] {tens : (∀ v, V v) → Vπ}

theorem Formalism.L2.SG.Pf.WuDec.norm_sub_tens_sq (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (x y : ∀ v, V v) :
    ‖tens x - tens y‖ ^ 2 = RCLike.re ((∏ v, ⟪x v, x v⟫_ℂ) - (∏ v, ⟪x v, y v⟫_ℂ) - (∏ v, ⟪y v, x v⟫_ℂ) +
      (∏ v, ⟪y v, y v⟫_ℂ)) := by sorry
