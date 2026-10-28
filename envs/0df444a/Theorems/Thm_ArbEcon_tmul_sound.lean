-- Prove2me | Theorems.Thm_ArbEcon_tmul_sound
-- name    : ArbEcon.tmul_sound
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:40:44.065014+00:00
-- url     : https://prove2.me/theorems/86fc8fc8-2f6a-4a3e-8b3e-d74b9689ec2e
-- title:
--   A fixed-point product error bound
-- statement:
--   Let $P,\ell,u,m,r$ be nonnegative integers, $Q=2^P$, $x\in[0,1]$, and $v$ real.
--   Let $\sigma\in\{-1,1\}$ be the sign selected by the supplied Boolean value.
--   Assume $\ell\le Qx\le u$, $m\le Q$, and $|Qv-\sigma m|\le r$. Then
--
--   $$\left|Qxv-\sigma\left\lfloor\frac{um}{Q}\right\rfloor\right|
--   \le\left\lfloor\frac{ur}{Q}\right\rfloor+(u-\ell)+2.$$
--
--   This bounds one fixed-point product in the zeta-series evaluator.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/Probes/ArbEconomics_Sound.lean#L906-L953

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



/-! ## D. the theta interval -/



/-! ## E. Horner: real recursion, closed form, fixed-point error -/


















/-! ## F. Taylor remainders for cos / sin through `Complex.exp_bound` -/





/-! ## G. cos / sin of theta: reduction, Taylor core, rotation -/


























/-! ## H. the zeta term, the term product, one step, the run -/

theorem ArbEcon.tmul_sound (P Rlo Rhi vm vr : ℕ) (vs : Bool) (x v : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hRlo : (Rlo : ℝ) ≤ x * 2 ^ P) (hRhi : x * 2 ^ P ≤ Rhi)
    (hv : |v * 2 ^ P - sgn vs * vm| ≤ vr) (hvm : vm ≤ 2 ^ P) :
    |x * v * 2 ^ P - sgn vs * ((Nat.shiftRight (Nat.mul Rhi vm) P : ℕ) : ℝ)|
      ≤ ((Nat.add (Nat.add (Nat.shiftRight (Nat.mul Rhi vr) P) (Nat.sub Rhi Rlo)) 2 : ℕ) : ℝ) := by sorry
