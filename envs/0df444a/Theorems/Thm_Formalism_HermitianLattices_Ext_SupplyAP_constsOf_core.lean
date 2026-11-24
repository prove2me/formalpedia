-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_constsOf_core
-- name    : Formalism.HermitianLattices.Ext.SupplyAP.constsOf_core
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:46.454441+00:00
-- url     : https://prove2.me/theorems/f2f071d1-4eb7-4a33-ac64-54ec2be8c6b7
-- title:
--   Supply AP: consts Of core
-- statement:
--   The Supply AP construction uses the consts Of core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffConsts.lean#L7-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffConsts.lean#L7-L111

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

theorem Formalism.HermitianLattices.Ext.SupplyAP.constsOf_core (n : ℕ) (c c₀ C R l T M : ℝ) (hn : 1 ≤ n) (hc : 0 < c) (hc₀ : 0 < c₀)
    (hC : 0 ≤ C)
    (hA1 : 4 * (n : ℝ) + 4 * (24 / c₀) ≤ R) (hA2 : (n : ℝ) + 2 * C / c₀ ≤ c * R) (hl : 1 ≤ l)
    (hT : R ^ 2 * l ^ 2 ≤ T) (hM : 0 < M) (hMl : M ≤ Real.exp l) :
    4 ≤ T ∧ M ≤ Real.exp (c * Real.sqrt T) ∧
      3 * (Real.exp (T / 2) * T) ≤
        c₀ * Real.exp T / M ^ n - C * Real.exp T * Real.exp (-c * Real.sqrt T) := by sorry
