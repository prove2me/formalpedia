-- Prove2me | Theorems.Thm_ArbEcon_horner_err
-- name    : ArbEcon.horner_err
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:38:38.301621+00:00
-- url     : https://prove2.me/theorems/d0b52929-cc9e-4dcf-b727-ab026532a6f7
-- title:
--   Fixed-point Horner evaluation has bounded error
-- statement:
--   Let $S>0$, $W,h$ be nonnegative integers, and let $w,r$ be real numbers with
--   $0\le w,r\le1$, $W\le Sw<W+1$, $W\le S$, $h\le S$, and $|h-Sr|\le3$.
--   Let $D$ be a finite list of integers, each at least $2$. Denote by $H$ the
--   fixed-point Horner evaluation with scale $S$, argument $W$, initial value $h$,
--   and divisors $Sd$ for $d\in D$; let $H_{\mathbb R}$ be the corresponding real
--   Horner evaluation at $w$, starting from $r$, with divisors $d\in D$. Then
--
--   $$H\le S,\qquad 0\le H_{\mathbb R}\le1,\qquad |H-SH_{\mathbb R}|\le3.$$
--
--   The two Horner functions are the evaluator operations defined in the accompanying
--   fixed-point and real-arithmetic bundles.
--
--   This bounds the accumulated rounding error in the evaluator.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/Probes/ArbEconomics_Sound.lean#L381-L456

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

theorem ArbEcon.horner_err (one wN : ℕ) (w : ℝ) (hone : 0 < one) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hwlo : (wN : ℝ) ≤ one * w) (hwhi : (one : ℝ) * w < wN + 1) (hwN : wN ≤ one) :
    ∀ (L : List ℕ) (hN : ℕ) (hR : ℝ), (∀ d ∈ L, 2 ≤ d) → hN ≤ one → 0 ≤ hR → hR ≤ 1 →
      |(hN : ℝ) - one * hR| ≤ 3 →
      horner one wN (L.map (fun d : ℕ => one * d)) hN ≤ one ∧
      0 ≤ hornerR w (L.map (fun d : ℕ => (d : ℝ))) hR ∧ hornerR w (L.map (fun d : ℕ => (d : ℝ))) hR ≤ 1 ∧
      |(horner one wN (L.map (fun d : ℕ => one * d)) hN : ℝ)
        - one * hornerR w (L.map (fun d : ℕ => (d : ℝ))) hR| ≤ 3 := by sorry
