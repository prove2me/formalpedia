-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_count_pos
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.count_pos
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:57.589801+00:00
-- url     : https://prove2.me/theorems/b6018841-dc5a-4907-9d75-bf3ffe49788d
-- title:
--   Logarithmic Integral Bounds: count pos
-- statement:
--   The Logarithmic Integral Bounds construction uses the count pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqCount.lean#L275-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqCount.lean#L275-L344

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.count_pos {c₃ A₀ C₀ c ε : ℝ} (hc₃ : 0 < c₃) (hcpos : 0 < c) (hc1 : c ≤ 1) (hε : 0 < ε)
    {m₀ : ℕ} [NeZero m₀] (h8 : 8 ∣ m₀) (a₀ : ℕ) (hcop : a₀.Coprime m₀)
    (e : Option (DirichletCharacter ℂ m₀ × ℝ))
    (he1 : ∀ p : DirichletCharacter ℂ m₀ × ℝ, e = some p → IsExcPair p.1 p.2)
    (he3 : ∀ (X : ℝ) (b : ℕ), 2 ≤ X → C₀ * Real.log m₀ * Real.log (Real.log m₀ + 2) ≤ Real.log X →
      b.Coprime m₀ → |(piAP X m₀ b : ℝ) - mainAP e b X| ≤
        A₀ * (Real.exp (-(c₃ * Real.log X / Real.log m₀)) + Real.exp (-Real.sqrt (c₃ * Real.log X))) *
          mainAP e b X)
    (hcb : ∀ (χ : DirichletCharacter ℂ m₀) (β : ℝ), χ ^ 2 = 1 → χ ≠ 1 →
      DirichletCharacter.LFunction χ (β : ℂ) = 0 → β ≤ 1 - c * (m₀ : ℝ) ^ (-1 : ℝ))
    (x X : ℝ) (hx1 : 1 ≤ x) (hl320 : 320 ≤ Real.log x)
    (hlC : 4 * |C₀| * (5 + ε / 5) ≤ Real.log x)
    (hlK1 : 4 * Real.log (4 * (|A₀| + 1)) / c₃ ≤ Real.log x)
    (hlK2 : 4 * Real.log (4 * (|A₀| + 1)) ^ 2 / c₃ ≤ Real.log x)
    (hlc : |Real.log (320 / c)| ≤ Real.log x)
    (h1 : (1 / 4) * Real.log x ^ 2 * Real.log m₀ ≤ Real.log X)
    (h3 : Real.log X ≤ x ^ (ε / 5) * Real.log x ^ 2) (hpos : 0 < X) :
    X ^ (9 / 10 : ℝ) ≤ ((PPset m₀ a₀ X).card : ℝ) := by sorry
