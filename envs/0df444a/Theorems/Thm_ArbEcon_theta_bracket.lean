-- Prove2me | Theorems.Thm_ArbEcon_theta_bracket
-- name    : ArbEcon.theta_bracket
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:54:14.23398+00:00
-- url     : https://prove2.me/theorems/35d2f97f-2d4b-47a4-ad9b-96141901e4cf
-- title:
--   Integer bracket for a scaled phase product
-- statement:
--   Let $P,t_n,t_q,L_{\rm lo},L_{\rm hi}\in\mathbb N$ and $L\in\mathbb R$ satisfy
--   $L_{\rm lo}\le2^P L\le L_{\rm hi}$. Then
--   $$\left\lfloor\frac{t_nL_{\rm lo}}{2^{t_q}}\right\rfloor
--   \le2^P\frac{t_n}{2^{t_q}}L
--   \le\left\lfloor\frac{t_nL_{\rm hi}}{2^{t_q}}\right\rfloor+1.$$
--   The endpoints are the defined natural-number right shifts and are cast to reals.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/Probes/ArbEconomics_Sound.lean#L276-L296

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

theorem ArbEcon.theta_bracket (P tn tq : ℕ) (L : ℝ) (lloN lhiN : ℕ)
    (hlo : (lloN : ℝ) ≤ L * 2 ^ P) (hhi : L * 2 ^ P ≤ lhiN) :
    ((Nat.shiftRight (Nat.mul tn lloN) tq : ℕ) : ℝ) ≤ ((tn : ℝ) / 2 ^ tq * L) * 2 ^ P ∧
    ((tn : ℝ) / 2 ^ tq * L) * 2 ^ P ≤ ((Nat.add (Nat.shiftRight (Nat.mul tn lhiN) tq) 1 : ℕ) : ℝ) := by sorry
