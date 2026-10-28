-- Prove2me | Theorems.Thm_ArbEcon_taylor_fixed
-- name    : ArbEcon.taylor_fixed
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:40:49.624659+00:00
-- url     : https://prove2.me/theorems/0eb10359-c128-4155-a6ec-3dfee12314b7
-- title:
--   Fixed-point sine and cosine evaluation bounds
-- statement:
--   Let $P,K,m,\tau$ be nonnegative integers, $Q=2^P$, and $16m\le13Q$.
--   Let $B_K=(13/16)^{2K+2}(2K+3)/((2K+2)!(2K+2))$ and assume $QB_K\le\tau$.
--   Put $w=\lfloor m^2/Q\rfloor$. Let $H(Q,w,D,h)$ be the defined integer Horner
--   evaluator, and let $D_c$ and $D_s$ be the respective descending divisor lists
--   $Q(2j-1)(2j)$ and $Q(2j)(2j+1)$ for $j=K,\ldots,1$. Define
--
--   $$C=H(Q,w,D_c,Q),\qquad S=\left\lfloor\frac{mH(Q,w,D_s,Q)}{Q}\right\rfloor.$$
--
--   Then
--
--   $$|C-Q\cos(m/Q)|\le3+\tau,\quad
--   |S-Q\sin(m/Q)|\le4+\tau,\quad C\le Q,\quad S\le Q.$$
--
--   This verifies the fixed-point Taylor core used by the trigonometric checker.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/Probes/ArbEconomics_Sound.lean#L584-L683

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
import Theorems.Thm_ArbEcon_cos_sin_taylor
import Theorems.Thm_ArbEcon_horner_err
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





/-! ## G. cos / sin of theta: reduction, Taylor core, rotation -/

theorem ArbEcon.taylor_fixed (P K mag tau : ℕ) (hmag : mag * 16 ≤ 13 * 2 ^ P)
    (htau : (2 : ℝ) ^ P * taylorBnd K ≤ tau) :
    let one := 2 ^ P
    let w := Nat.shiftRight (Nat.mul mag mag) P
    let C := horner one w ((divList fcos K).map (fun d : ℕ => one * d)) one
    let S0 := Nat.shiftRight (Nat.mul mag (horner one w ((divList fsin K).map (fun d : ℕ => one * d)) one)) P
    |(C : ℝ) - 2 ^ P * Real.cos ((mag : ℝ) / 2 ^ P)| ≤ 3 + tau ∧
    |(S0 : ℝ) - 2 ^ P * Real.sin ((mag : ℝ) / 2 ^ P)| ≤ 4 + tau ∧ C ≤ one ∧ S0 ≤ one := by sorry
