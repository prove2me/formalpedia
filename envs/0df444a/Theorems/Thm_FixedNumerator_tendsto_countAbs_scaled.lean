-- Prove2me | Theorems.Thm_FixedNumerator_tendsto_countAbs_scaled
-- name    : FixedNumerator.tendsto_countAbs_scaled
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:40:21.450984+00:00
-- url     : https://prove2.me/theorems/bba8fe1e-bfa5-5ffe-a78f-8eba98be2d42
-- title:
--   Fixed Numerator: tendsto count Abs scaled
-- statement:
--   `countAbs a (t X) / X → κ t` for `t > 0`.
--
--   Source: https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Sharp.lean#L29-L39
-- source:
--   https://github.com/jkfarland-bot/FixedNumerator/blob/817fb1416c9d54140c6bbdd9b2d08f37b481d934/FixedNumerator/Sharp.lean#L29-L39

module
public import Definitions.Def_FixedNumerator_Determinant
public import Definitions.Def_FixedNumerator_Sharp
set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Filter Asymptotics Topology
open scoped ContDiff
open FixedNumerator

theorem FixedNumerator.tendsto_countAbs_scaled {a : ℕ → ℂ} {κ : ℝ}
    (hmean : Tendsto (fun x : ℝ => countAbs a x / x) atTop (𝓝 κ)) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun X : ℕ => countAbs a (t * X) / X) atTop (𝓝 (κ * t)) := by sorry
