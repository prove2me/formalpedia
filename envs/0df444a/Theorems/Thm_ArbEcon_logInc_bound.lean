-- Prove2me | Theorems.Thm_ArbEcon_logInc_bound
-- name    : ArbEcon.logInc_bound
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:39:27.402969+00:00
-- url     : https://prove2.me/theorems/a68662d0-50e4-4412-9d51-4d84edf5318e
-- title:
--   Fixed-point enclosure for a logarithmic increment
-- statement:
--   Let $P$ and $K$ be nonnegative integers, $m\ge2$, and $S=2^P$. Put
--
--   $$A=\sum_{i=0}^{K-1}\left\lfloor\frac{S}{m^{i+1}(i+1)}\right\rfloor,
--   \qquad W=m^{K+1}.$$
--
--   Then
--
--   $$A\le S\bigl(\log m-\log(m-1)\bigr)
--   \le A+K+\left\lfloor\frac{2^{P+1}}{W}\right\rfloor+1.$$
--
--   This is the logarithm increment enclosure used by the integer evaluator.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/Probes/ArbEconomics_Sound.lean#L127-L198

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

theorem ArbEcon.logInc_bound (P m : ℕ) (hm : 2 ≤ m) (r : ℕ × ℕ × ℕ) (hr : LogSpec (2 ^ P) m r) :
    (r.1 : ℝ) ≤ (Real.log m - Real.log ((m : ℝ) - 1)) * 2 ^ P ∧
    (Real.log m - Real.log ((m : ℝ) - 1)) * 2 ^ P
      ≤ (r.1 : ℝ) + r.2.1 + ((2 ^ (P + 1) / r.2.2 : ℕ) + 1) := by sorry
