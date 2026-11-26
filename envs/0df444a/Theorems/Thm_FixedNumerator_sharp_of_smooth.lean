-- Prove2me | Theorems.Thm_FixedNumerator_sharp_of_smooth
-- name    : FixedNumerator.sharp_of_smooth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:43:46.005207+00:00
-- url     : https://prove2.me/theorems/d00ea68a-4be0-5351-b061-e874e60d590a
-- title:
--   Fixed Numerator: sharp of smooth
-- statement:
--   **Corollary 1.2: removing the smoothing.**
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Sharp.lean#L42-L164
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Sharp.lean#L42-L164

module
public import Definitions.Def_FixedNumerator_Determinant
public import Definitions.Def_FixedNumerator_Sharp
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Filter Asymptotics Topology
open scoped ContDiff
open FixedNumerator

theorem FixedNumerator.sharp_of_smooth (a : ℕ → ℂ) (κ : ℝ)
    (hmean : Tendsto (fun x : ℝ => countAbs a x / x) atTop (𝓝 κ))
    (hsmooth : ∀ R : ℝ → ℝ, ContDiff ℝ ∞ R → (∃ δ > 0, Function.support R ⊆ Set.Icc δ 1) →
      (fun X : ℕ => smoothSum a R X) =o[atTop] (fun X : ℕ => (X : ℝ))) :
    (fun X : ℕ => sharpSum a X) =o[atTop] (fun X : ℕ => (X : ℝ)) := by sorry
