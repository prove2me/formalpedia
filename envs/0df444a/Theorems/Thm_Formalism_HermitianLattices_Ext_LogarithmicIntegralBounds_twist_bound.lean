-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_twist_bound
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.twist_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:29.879133+00:00
-- url     : https://prove2.me/theorems/e02a8824-53a4-4404-aad4-25e27b270698
-- title:
--   Logarithmic Integral Bounds: twist bound
-- statement:
--   The Logarithmic Integral Bounds construction uses the twist bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqTwist.lean#L18-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqTwist.lean#L18-L227

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqOrth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqPage
import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistB
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistC
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwist
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
set_option maxHeartbeats 1000000

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.twist_bound (hP : PNTAPRelW) (hZ : Formalism.ZeroFreeDirichlet.ZFRDirichlet) (hE : Formalism.ZeroFreeDirichlet.ExcBound) (ε : ℝ) (hε : 0 < ε) :
    ∃ x₀ : ℝ, ∀ (x X : ℝ) (m₀ a₀ : ℕ),
    x₀ ≤ x → 0 < m₀ → 8 ∣ m₀ → a₀.Coprime m₀ →
    (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X → x ^ (ε / 6) ≤ Real.log X →
    Real.log X ≤ x ^ (ε / 5) * Real.log x ^ 2 →
    ∃ nstar : ℕ, ∀ s : ℕ, 1 < s → Odd s → Squarefree s → s.Coprime m₀ → s ≤ ⌊x ^ 400⌋₊ ^ 2 → s ≠ nstar →
      |∑ q ∈ PPset m₀ a₀ X, (jacobiSym (q : ℤ) s : ℝ)| ≤ x ^ (-3 : ℝ) * ((PPset m₀ a₀ X).card : ℝ) := by sorry
