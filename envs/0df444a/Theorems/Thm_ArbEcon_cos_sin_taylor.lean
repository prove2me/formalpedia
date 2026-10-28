-- Prove2me | Theorems.Thm_ArbEcon_cos_sin_taylor
-- name    : ArbEcon.cos_sin_taylor
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:39:41.140134+00:00
-- url     : https://prove2.me/theorems/ff2628fb-a0ac-444f-a600-394307d86055
-- title:
--   Common error bound for truncated sine and cosine series
-- statement:
--   Let $0\le u\le1$ be real and let $K$ be a nonnegative integer. Define
--
--   $$C_K(u)=\sum_{j=0}^{K}\frac{(-1)^ju^{2j}}{(2j)!},\qquad
--   S_K(u)=\sum_{j=0}^{K}\frac{(-1)^ju^{2j+1}}{(2j+1)!},$$
--
--   and put $E=u^{2K+2}(2K+3)/((2K+2)!(2K+2))$. Then
--
--   $$|\cos u-C_K(u)|\le E,\qquad |\sin u-S_K(u)|\le E.$$
--
--   These truncation bounds support the fixed-point trigonometric evaluator.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/Probes/ArbEconomics_Sound.lean#L480-L518

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
import Theorems.Thm_ArbEcon_expI_partial
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



/-! ## D. the theta interval -/



/-! ## E. Horner: real recursion, closed form, fixed-point error -/


















/-! ## F. Taylor remainders for cos / sin through `Complex.exp_bound` -/

theorem ArbEcon.cos_sin_taylor (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (K : ℕ) :
    |Real.cos u - hornerR (u ^ 2) ((divList fcos K).map (fun d : ℕ => (d : ℝ))) 1|
      ≤ u ^ (2 * K + 2) * (((2 * K + 2).succ : ℝ) * (((2 * K + 2).factorial : ℝ) * (2 * K + 2 : ℕ))⁻¹) ∧
    |Real.sin u - u * hornerR (u ^ 2) ((divList fsin K).map (fun d : ℕ => (d : ℝ))) 1|
      ≤ u ^ (2 * K + 2) * (((2 * K + 2).succ : ℝ) * (((2 * K + 2).factorial : ℝ) * (2 * K + 2 : ℕ))⁻¹) := by sorry
