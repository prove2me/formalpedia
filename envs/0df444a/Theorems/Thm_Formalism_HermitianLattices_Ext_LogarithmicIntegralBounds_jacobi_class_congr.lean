-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_jacobi_class_congr
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.jacobi_class_congr
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:34.931799+00:00
-- url     : https://prove2.me/theorems/94415a46-6c51-4d30-9f73-3ae65c6e0607
-- title:
--   Logarithmic Integral Bounds: jacobi class congr
-- statement:
--   The Logarithmic Integral Bounds construction uses the jacobi class congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqJac.lean#L117-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqJac.lean#L117-L139

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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.jacobi_class_congr {m₀ N q q' : ℕ} (h8 : 8 ∣ m₀) (hN : 0 < N) (hq : q.Prime) (hq' : q'.Prime)
    (hqq : q % m₀ = q' % m₀) (hNq : N < q) (hNq' : N < q') :
    jacobiSym (N : ℤ) q * jacobiSym (q : ℤ) (soutPart m₀ N) =
      jacobiSym (N : ℤ) q' * jacobiSym (q' : ℤ) (soutPart m₀ N) := by sorry
