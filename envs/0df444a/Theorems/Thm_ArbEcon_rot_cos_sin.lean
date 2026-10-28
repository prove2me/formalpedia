-- Prove2me | Theorems.Thm_ArbEcon_rot_cos_sin
-- name    : ArbEcon.rot_cos_sin
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:39:43.669002+00:00
-- url     : https://prove2.me/theorems/590315cd-e7ec-4d91-9611-fe4fb9827839
-- title:
--   Quadrant rotation formulas
-- statement:
--   For a real angle $\phi$ and a nonnegative integer $k$, let
--   $C=\cos(\phi+k\pi/2)$ and $S=\sin(\phi+k\pi/2)$. According to $k$ modulo $4$,
--
--   $$ (C,S)=\begin{cases}
--   (\cos\phi,\sin\phi),&k\equiv0\pmod4,\\
--   (-\sin\phi,\cos\phi),&k\equiv1\pmod4,\\
--   (-\cos\phi,-\sin\phi),&k\equiv2\pmod4,\\
--   (\sin\phi,-\cos\phi),&k\equiv3\pmod4.
--   \end{cases} $$
--
--   These identities return reduced angles to their original quadrants.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/Probes/ArbEconomics_Sound.lean#L685-L708

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

theorem ArbEcon.rot_cos_sin (φ : ℝ) (k : ℕ) :
    (k % 4 = 0 → Real.cos (φ + k * (π / 2)) = Real.cos φ ∧ Real.sin (φ + k * (π / 2)) = Real.sin φ) ∧
    (k % 4 = 1 → Real.cos (φ + k * (π / 2)) = -Real.sin φ ∧ Real.sin (φ + k * (π / 2)) = Real.cos φ) ∧
    (k % 4 = 2 → Real.cos (φ + k * (π / 2)) = -Real.cos φ ∧ Real.sin (φ + k * (π / 2)) = -Real.sin φ) ∧
    (k % 4 = 3 → Real.cos (φ + k * (π / 2)) = Real.sin φ ∧ Real.sin (φ + k * (π / 2)) = -Real.cos φ) := by sorry
