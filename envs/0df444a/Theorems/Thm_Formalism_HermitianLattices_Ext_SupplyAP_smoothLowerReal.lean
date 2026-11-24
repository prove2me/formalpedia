-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_smoothLowerReal
-- name    : Formalism.HermitianLattices.Ext.SupplyAP.smoothLowerReal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:01.719398+00:00
-- url     : https://prove2.me/theorems/e0d33453-5459-46e6-aa2d-662436ed8ef4
-- title:
--   Supply AP: smooth Lower Real
-- statement:
--   The Supply AP construction uses the smooth Lower Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffSmooth.lean#L160-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffSmooth.lean#L160-L228

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffBase
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffSmooth
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
open Finset
open scoped ComplexOrder

theorem Formalism.HermitianLattices.Ext.SupplyAP.smoothLowerReal (c r : ℕ → ℝ) (hr : ∀ n, r n = ∑ d ∈ n.divisors, c d)
    (hc : ∀ d, |c d| ≤ 1) (hr0 : ∀ n, 0 ≤ r n) (hr1 : ∀ k, k ≠ 0 → 1 ≤ r (k ^ 2))
    (K N : ℕ) (x : ℝ) (hx : 0 < x) (hKx : (K : ℝ) ^ 2 ≤ x) (hKN : K ^ 2 ≤ N) :
    (K : ℝ) / Real.exp 1 ≤
      x * (∑ d ∈ Icc 1 N, c d / (d : ℝ)) + (∑ d ∈ Icc 1 N, c d * gExp ((d : ℝ) / x)) +
      (N : ℝ) * (x + 1) * Real.exp (-(N : ℝ) / x) := by sorry
