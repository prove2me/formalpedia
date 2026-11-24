-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_sum_jacobiSym_eq_sum_residueClass
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.sum_jacobiSym_eq_sum_residueClass
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:50.432065+00:00
-- url     : https://prove2.me/theorems/149e2064-9113-4da7-8c12-465c021491a5
-- title:
--   Logarithmic Integral Bounds: sum jacobi Sym eq sum residue Class
-- statement:
--   The Logarithmic Integral Bounds construction uses the sum jacobi Sym eq sum residue Class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqTwistA.lean#L19-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqTwistA.lean#L19-L65

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqOrth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistA
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
open Formalism.HermitianLattices.ZeroFreeRegionGL2

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.sum_jacobiSym_eq_sum_residueClass (m₀ s a₀ : ℕ) (X : ℝ) (hm : 0 < m₀) (hs : 0 < s) :
    ∑ q ∈ PPset m₀ a₀ X, (jacobiSym (q : ℤ) s : ℝ) =
      ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) *
        (((PPset m₀ a₀ X).filter (fun q => q % (m₀ * s) = b)).card : ℝ) := by sorry
