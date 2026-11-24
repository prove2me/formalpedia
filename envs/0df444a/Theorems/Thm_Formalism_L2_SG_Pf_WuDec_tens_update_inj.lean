-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_WuDec_tens_update_inj
-- name    : Formalism.L2.SG.Pf.WuDec.tens_update_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:54.20142+00:00
-- url     : https://prove2.me/theorems/0c5ce057-97a9-42d4-9618-5b733cc39922
-- title:
--   Wu Dec: tens update inj
-- statement:
--   The Wu Dec construction uses the tens update inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/TensInt.lean#L77-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/TensInt.lean#L77-L94

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

theorem Formalism.L2.SG.Pf.WuDec.tens_update_inj [DecidableEq ι] (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (ξ : ∀ v, V v)
    (v : ι) (hne : ∀ w, w ≠ v → ξ w ≠ 0) (a b : V v)
    (h : tens (Function.update ξ v a) = tens (Function.update ξ v b)) : a = b := by sorry
