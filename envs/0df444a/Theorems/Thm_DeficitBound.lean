-- Prove2me | Theorems.Thm_DeficitBound
-- name    : DeficitBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:54:17.766023+00:00
-- url     : https://prove2.me/theorems/9d0b26ce-2ef9-4d62-b9cd-da0c93332c5f
-- title:
--   Deficit Bound: Deficit Bound
-- statement:
--   The paper's deficit estimate at the first Chebyshev node (Lemma 2.2):
--   for a real trigonometric polynomial `T` of degree at most `m ≥ 2` with
--   `|T| ≤ 1` and `T 0 = 1`, writing `d = m^2 + T''(0)`, one has
--   `0 ≤ 1 + T (±π/m) ≤ d (1 - cos (π/m)) ≤ π^2 d / (2 m^2)`.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/DeficitBound.lean#L14-L122
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/DeficitBound.lean#L14-L122

module
public import Definitions.Def_PHarmonicPoly_DeficitPoly
public import Definitions.Def_PHarmonicPoly_TrigPolyEvenPart
public import Definitions.Def_PHarmonicPoly_PolyCosSecondDeriv
public import Definitions.Def_PHarmonicPoly_TrigPolySmooth
public import Definitions.Def_PHarmonicPoly_DeficitBound
public import Theorems.Thm_DeficitPoly
public import Theorems.Thm_PolyCosSecondDeriv
public import Theorems.Thm_TrigPolyEvenPart
public import Theorems.Thm_TrigPolySmooth

set_option autoImplicit false
@[expose] public section
public section

theorem DeficitBound {m : ℕ} (hm : 2 ≤ m) {T : ℝ → ℝ} (hT : TrigPolyLe m T)
    (hbd : ∀ t : ℝ, |T t| ≤ 1) (h0 : T 0 = 1) :
    (0 ≤ 1 + T (Real.pi / m) ∧ 0 ≤ 1 + T (-(Real.pi / m)))
      ∧ (1 + T (Real.pi / m)
            ≤ ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) * (1 - Real.cos (Real.pi / m))
          ∧ 1 + T (-(Real.pi / m))
            ≤ ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) * (1 - Real.cos (Real.pi / m)))
      ∧ ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) * (1 - Real.cos (Real.pi / m))
          ≤ Real.pi ^ 2 * ((m : ℝ) ^ 2 + iteratedDeriv 2 T 0) / (2 * (m : ℝ) ^ 2) := by sorry
