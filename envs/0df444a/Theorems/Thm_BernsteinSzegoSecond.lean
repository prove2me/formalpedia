-- Prove2me | Theorems.Thm_BernsteinSzegoSecond
-- name    : BernsteinSzegoSecond
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:59:02.766003+00:00
-- url     : https://prove2.me/theorems/0a8200ce-8239-4c59-a7f9-2d6b09825319
-- title:
--   Bernstein Szego Second: Bernstein Szego Second
-- statement:
--   The second form of the paper's eq:bernstein, obtained by applying the
--   Bernstein-Szego inequality to `T'/m`: `(T')^2/m^2 + (T'')^2/m^4 ≤ 1`.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/BernsteinSzegoSecond.lean#L12-L54
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/BernsteinSzegoSecond.lean#L12-L54

module
public import Definitions.Def_PHarmonicPoly_BernsteinSzego
public import Definitions.Def_PHarmonicPoly_TrigPolyDeriv
public import Definitions.Def_PHarmonicPoly_TrigPolyLinComb
public import Definitions.Def_PHarmonicPoly_TrigPolySmooth
public import Definitions.Def_PHarmonicPoly_BernsteinSzegoSecond
public import Theorems.Thm_BernsteinSzego
public import Theorems.Thm_TrigPolyDeriv
public import Theorems.Thm_TrigPolyLinComb
public import Theorems.Thm_TrigPolySmooth

set_option autoImplicit false
@[expose] public section
public section

theorem BernsteinSzegoSecond {m : ℕ} (hm : 1 ≤ m) {T : ℝ → ℝ}
    (hT : TrigPolyLe m T) (hbd : ∀ t : ℝ, |T t| ≤ 1) :
    ∀ t : ℝ,
      (deriv T t) ^ 2 / (m : ℝ) ^ 2
        + (iteratedDeriv 2 T t) ^ 2 / (m : ℝ) ^ 4 ≤ 1 := by sorry
