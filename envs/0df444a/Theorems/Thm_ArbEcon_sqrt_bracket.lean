-- Prove2me | Theorems.Thm_ArbEcon_sqrt_bracket
-- name    : ArbEcon.sqrt_bracket
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:40:39.401155+00:00
-- url     : https://prove2.me/theorems/1ac8a69e-c254-46c7-800a-2fafff959f32
-- title:
--   Integer brackets for a scaled reciprocal square root
-- statement:
--   Let $P,g$ be nonnegative integers and $m\ge1$. Put $Q=2^P$. If $g=0$, set
--   $L=0$ and $U=Q$. If $g>0$ and $mg^2\le Q^2$, set $L=g$ and
--   $U=\lfloor Q^2/(mg)\rfloor+1$; otherwise set
--   $L=\lfloor Q^2/(mg)\rfloor$ and $U=g$. Then
--
--   $$L\le\frac{Q}{\sqrt m}\le U.$$
--
--   These integer bounds certify the evaluator’s reciprocal-square-root enclosure.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/Probes/ArbEconomics_Sound.lean#L202-L272

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRS_Arithmetic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.IntervalCases
/-  Probes/ArbEconomics_Sound.lean -- soundness of the Nat-only zeta evaluator (ArbEconomics_Eval).

    Every function of `ArbEconomics_Eval` is shown to produce a TRUE enclosure:
      * `logInc`   : `S <= (log m - log (m-1)) 2^P <= S + K + T`
                     (Mathlib `Real.hasSum_pow_div_log_of_abs_lt_one`, `abs_log_sub_add_sum_range_le`);
      * `termOf`   : `Rlo <= 2^P / sqrt m <= Rhi` for ANY Newton iterate (two-sided validation);
      * `trig`     : cos/sin balls of `theta` from the (pi/2)-reduction, the Horner scheme
                     (Mathlib `Complex.exp_bound`) and the quadrant rotation;
      * `step`/`run` : the loop invariant `Inv` (log bracket + Re/Im balls of the partial zeta sum).

    The main theorem `run_sound` turns a kernel-checked chunk equation
    `St.beq (run cfg L s) s' = true` into `Inv n s -> Inv (n + L) s'`.

    conjecture1_proved = False.  Finite interval arithmetic; nothing here is about RH.
-/










open Real Finset

section
namespace ArbEcon
end ArbEcon
open ArbEcon

/-! ## A. floor division / shifts, cast to ℝ -/











/-! The evaluator calls the kernel primitives directly; these `rfl` lemmas translate them back to
    notation for the proofs. -/










/-! ## B. the log increment -/











/-! ## C. the square-root bracket -/

theorem ArbEcon.sqrt_bracket (P m g : ℕ) (hm : 1 ≤ m) :
    ((Bool.rec 0 (Bool.rec (Nat.div (2 ^ (2 * P)) (Nat.mul m g)) g
        (Nat.ble (Nat.mul (Nat.mul g g) m) (2 ^ (2 * P)))) (Nat.ble 1 g) : ℕ) : ℝ)
        ≤ (2 : ℝ) ^ P / Real.sqrt m ∧
    (2 : ℝ) ^ P / Real.sqrt m ≤ ((Bool.rec (2 ^ P) (Bool.rec g
        (Nat.add (Nat.div (2 ^ (2 * P)) (Nat.mul m g)) 1)
        (Nat.ble (Nat.mul (Nat.mul g g) m) (2 ^ (2 * P)))) (Nat.ble 1 g) : ℕ) : ℝ) := by sorry
