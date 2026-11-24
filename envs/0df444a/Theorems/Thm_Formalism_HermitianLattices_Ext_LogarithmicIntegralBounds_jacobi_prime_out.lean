-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_jacobi_prime_out
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.jacobi_prime_out
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:09.33148+00:00
-- url     : https://prove2.me/theorems/23e8ee6d-f5f1-4dde-ad78-050195f20daf
-- title:
--   Logarithmic Integral Bounds: jacobi prime out
-- statement:
--   The Logarithmic Integral Bounds construction uses the jacobi prime out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqJac.lean#L87-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqJac.lean#L87-L100

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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.jacobi_prime_out {m₀ p q q' : ℕ} (h8 : 8 ∣ m₀) (hp : p.Prime) (hpm : ¬ p ∣ m₀) (hq : q.Prime)
    (hq' : q'.Prime) (hqq : q % m₀ = q' % m₀) (hpq : p < q) (hpq' : p < q') :
    jacobiSym (p : ℤ) q * jacobiSym (q : ℤ) p = jacobiSym (p : ℤ) q' * jacobiSym (q' : ℤ) p := by sorry
