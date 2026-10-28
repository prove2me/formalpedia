-- Prove2me | Theorems.Thm_ArbEcon_phi_ball
-- name    : ArbEcon.phi_ball
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:39:32.939791+00:00
-- url     : https://prove2.me/theorems/cfbda384-263f-40bf-8aef-63f6c18dfef4
-- title:
--   Fixed-point enclosure after reduction by multiples of pi over two
-- statement:
--   Let $P,h,r,k,\ell,u$ be nonnegative integers, $Q=2^P$, and $\theta$ real. Assume
--   $\ell\le Q\theta\le u$ and $|Q\pi/2-h|\le r$. Put
--   $D=\ell+u-2kh$ and let $M=\operatorname{sgn}_{+}(D)\lfloor |D|/2\rfloor$,
--   where $\operatorname{sgn}_{+}(D)$ is $1$ for $D\ge0$ and $-1$ otherwise. Then
--
--   $$\left|Q\left(\theta-\frac{k\pi}{2}\right)-M\right|
--   \le\left\lfloor\frac{u-\ell}{2}\right\rfloor+kr+2.$$
--
--   This is the angle-reduction error bound used by the trigonometric evaluator.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/Probes/ArbEconomics_Sound.lean#L534-L578

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

theorem ArbEcon.phi_ball (P hp rp k thlo thhi : ℕ) (θ : ℝ)
    (hlo : (thlo : ℝ) ≤ θ * 2 ^ P) (hhi : θ * 2 ^ P ≤ thhi)
    (hpi : |Real.pi / 2 * 2 ^ P - hp| ≤ rp) :
    |(θ - k * (Real.pi / 2)) * 2 ^ P
        - sgn (Nat.ble (Nat.shiftLeft (Nat.mul k hp) 1) (Nat.add thlo thhi))
          * ((Nat.shiftRight (Bool.rec (Nat.sub (Nat.shiftLeft (Nat.mul k hp) 1) (Nat.add thlo thhi))
              (Nat.sub (Nat.add thlo thhi) (Nat.shiftLeft (Nat.mul k hp) 1))
              (Nat.ble (Nat.shiftLeft (Nat.mul k hp) 1) (Nat.add thlo thhi))) 1 : ℕ) : ℝ)|
      ≤ ((Nat.add (Nat.add (Nat.shiftRight (Nat.sub thhi thlo) 1) (Nat.mul k rp)) 2 : ℕ) : ℝ) := by sorry
