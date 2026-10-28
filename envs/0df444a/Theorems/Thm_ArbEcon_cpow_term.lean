-- Prove2me | Theorems.Thm_ArbEcon_cpow_term
-- name    : ArbEcon.cpow_term
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:38:38.413528+00:00
-- url     : https://prove2.me/theorems/36f461f9-8451-4824-8515-0e471bf3d7d7
-- title:
--   Real and imaginary parts of a zeta-series term
-- statement:
--   For a positive integer $m$ and a real number $t$,
--
--   $$\operatorname{Re}\!\left(m^{-1/2-it}\right)
--   =\frac{\cos(t\log m)}{\sqrt m},\qquad
--   \operatorname{Im}\!\left(m^{-1/2-it}\right)
--   =-\frac{\sin(t\log m)}{\sqrt m}.$$
--
--   These identities relate complex zeta-series terms to real trigonometric evaluations.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/Probes/ArbEconomics_Sound.lean#L884-L904

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

theorem ArbEcon.cpow_term (m : ℕ) (hm : 0 < m) (t : ℝ) :
    ((m : ℂ) ^ (-((1 : ℂ) / 2 + (t : ℂ) * Complex.I))).re = 1 / Real.sqrt m * Real.cos (t * Real.log m) ∧
    ((m : ℂ) ^ (-((1 : ℂ) / 2 + (t : ℂ) * Complex.I))).im = -(1 / Real.sqrt m * Real.sin (t * Real.log m)) := by sorry
