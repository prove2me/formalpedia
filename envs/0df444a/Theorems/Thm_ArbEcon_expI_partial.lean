-- Prove2me | Theorems.Thm_ArbEcon_expI_partial
-- name    : ArbEcon.expI_partial
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:38:41.752949+00:00
-- url     : https://prove2.me/theorems/52624d01-7b2a-4fc3-bf1d-7e095f8fde0f
-- title:
--   Even and odd parts of a truncated complex exponential
-- statement:
--   For every real $u$ and nonnegative integer $K$,
--
--   $$\sum_{m=0}^{2K-1}\frac{(iu)^m}{m!}
--   =\sum_{j=0}^{K-1}\frac{(-1)^j u^{2j}}{(2j)!}
--   +iu\sum_{j=0}^{K-1}\frac{(-1)^j u^{2j}}{(2j+1)!}.$$
--
--   An empty sum is zero.
--
--   This separates the even and odd Taylor terms used for cosine and sine bounds.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/Probes/ArbEconomics_Sound.lean#L460-L478

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

theorem ArbEcon.expI_partial (u : ℝ) : ∀ K : ℕ,
    ∑ m ∈ range (2 * K), ((u : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)
      = ((∑ j ∈ range K, (-1) ^ j * (u ^ 2) ^ j / ((2 * j).factorial : ℝ) : ℝ) : ℂ)
        + ((u * ∑ j ∈ range K, (-1) ^ j * (u ^ 2) ^ j / ((2 * j + 1).factorial : ℝ) : ℝ) : ℂ)
          * Complex.I := by sorry
