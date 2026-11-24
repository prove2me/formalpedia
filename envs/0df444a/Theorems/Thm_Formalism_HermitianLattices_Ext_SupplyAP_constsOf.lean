-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_constsOf
-- name    : Formalism.HermitianLattices.Ext.SupplyAP.constsOf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:49.040386+00:00
-- url     : https://prove2.me/theorems/8e40c4d4-05c5-45cc-b744-9cf466ce6717
-- title:
--   Supply AP: consts Of
-- statement:
--   The Supply AP construction uses the consts Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffConsts.lean#L113-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffConsts.lean#L113-L147

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffConsts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP

theorem Formalism.HermitianLattices.Ext.SupplyAP.constsOf (A : ℕ) (c c₀ C : ℝ) (hc : 0 < c) (hc₀ : 0 < c₀) (hC : 0 ≤ C) : ∃ K : ℝ, 4 ≤ K ∧
    ∀ (m : ℕ) (x : ℝ), 1 ≤ m → 0 < x → K * Real.log (3 * m) ^ 2 ≤ Real.log x →
      4 ≤ Real.log x ∧ (m : ℝ) ≤ Real.exp (c * Real.sqrt (Real.log x)) ∧
      3 * (Real.sqrt x * Real.log x) ≤
        c₀ * x / (m : ℝ) ^ (A + 1) - C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by sorry
