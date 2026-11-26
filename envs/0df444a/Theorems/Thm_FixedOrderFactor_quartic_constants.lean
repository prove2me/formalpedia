-- Prove2me | Theorems.Thm_FixedOrderFactor_quartic_constants
-- name    : FixedOrderFactor.quartic_constants
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T01:07:23.428234+00:00
-- url     : https://prove2.me/theorems/835df65e-55cf-4730-86e0-77d4e9724149
-- title:
--   Fixed Order Factor: quartic constants
-- statement:
--   The constants of the quartic family. Two baselines are involved and are kept apart here.
--   `zetaN {two} 2 = π²/8` is the factor-removed full-family value (the limit in Louboutin's
--   Théorème 3, with the Euler factor at `2` removed); it is not stated in this theorem. The first
--   conjunct, `(4/5) · zetaN {two} 2 = π²/10`, is a different comparison value: the full-family
--   model with the factor at `2` reinserted as the single value `4/5 = |1 ∓ i/2|⁻²` that the
--   congruence `p ≡ 5 (mod 8)` forces for quartic characters. The second conjunct multiplies this by
--   the correction factor `35/34`, giving the order-four value `7π²/68` with the same forced factor.
--   The third is the naive random Euler product `ζ(2) · ζ(4)²/ζ(8) = 7π²/36`, with `χ(2)` uniform on
--   the fourth roots of unity. The last two conjuncts are the arithmetic relations
--   `7/136 = (1/20)(35/34) = (7/72)(9/17)` between the corresponding means of `h⁻/p`.
--
--   Source: https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L108-L113
-- source:
--   https://github.com/jkfarland-bot/FixedOrderFactor-lean/blob/74f4fc5b5253c181a2ba67bf3220a7c0b5fcf6fd/Solution.lean#L108-L113

module
public import Definitions.Def_FixedOrderFactor
public import Definitions.Def_FixedOrderFactor_Solution
set_option autoImplicit true
@[expose] public section
public section
open Real Filter Topology
noncomputable section
open FixedOrderFactor

theorem FixedOrderFactor.quartic_constants :
    (4 / 5) * zetaN {two} 2 = π ^ 2 / 10 ∧
    (4 / 5) * zetaN {two} 2 * correctionFactor {two} 4 = 7 * π ^ 2 / 68 ∧
    zetaN ∅ 2 * correctionFactor ∅ 4 = 7 * π ^ 2 / 36 ∧
    (7 : ℝ) / 136 = 1 / 20 * (35 / 34) ∧ (7 : ℝ) / 136 = 7 / 72 * (9 / 17) := by sorry
