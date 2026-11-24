-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_twist_one
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.twist_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:07.121003+00:00
-- url     : https://prove2.me/theorems/96e4422d-ea61-4189-92f4-b8f64a480d95
-- title:
--   Logarithmic Integral Bounds: twist one
-- statement:
--   The Logarithmic Integral Bounds construction uses the twist one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqTwistB.lean#L221-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqTwistB.lean#L221-L240

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistB
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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.twist_one (m₀ s a₀ : ℕ) [NeZero (m₀ * s)] (hm : 0 < m₀) (h1 : 1 < s) (hodd : Odd s)
    (hsq : Squarefree s) (hcop : m₀.Coprime s) (ha : a₀.Coprime m₀) (X r k : ℝ)
    (e : Option (DirichletCharacter ℂ (m₀ * s) × ℝ)) (hX : 0 ≤ X) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2)
    (hli : 0 < liX X) (hk : |k| ≤ 1 / 2)
    (hb : ∀ b ∈ clsB m₀ s a₀, |(piAP X (m₀ * s) b : ℝ) - mainAP e b X| ≤ k * mainAP e b X)
    (hG : ∀ (χ : DirichletCharacter ℂ (m₀ * s)) (β : ℝ), e = some (χ, β) →
      (∀ u : ℕ, u % m₀ = 1 % m₀ → u.Coprime s → χ (u : ZMod (m₀ * s)) = ((jacobiSym (u : ℤ) s : ℤ) : ℂ)) →
      |liX (X ^ β)| ≤ r * liX X) :
    |∑ q ∈ PPset m₀ a₀ X, (jacobiSym (q : ℤ) s : ℝ)| ≤
      (4 * r + 2 * |k|) * (((PPset m₀ a₀ X).card : ℝ) + X ^ (1 / 2 : ℝ)) + X ^ (1 / 2 : ℝ) := by sorry
