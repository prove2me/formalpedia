-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_gcd_prime_lt
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.gcd_prime_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:18:50.441842+00:00
-- url     : https://prove2.me/theorems/e0f073b8-a8fa-4e1d-806c-cdc8f282b36b
-- title:
--   Logarithmic Integral Bounds: gcd prime lt
-- statement:
--   The Logarithmic Integral Bounds construction uses the gcd prime lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqJac.lean#L60-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqJac.lean#L60-L67

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqJac
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.gcd_prime_lt {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    ((p : ℤ).gcd (q : ℤ) = 1) ∧ ((q : ℤ).gcd (p : ℤ) = 1) := by sorry
