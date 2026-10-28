-- Prove2me | Theorems.Thm_ArbEcon_trig_sound
-- name    : ArbEcon.trig_sound
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:42:10.550764+00:00
-- url     : https://prove2.me/theorems/b5560fb3-ce98-45bb-be46-c6d9756d54f5
-- title:
--   Soundness of fixed-point sine and cosine enclosures
-- statement:
--   Let $c$ be a valid evaluator configuration at real height $t$ and order $K$,
--   with precision $P$, and let $\ell,u$ be nonnegative integers satisfying
--   $\ell\le2^P\theta\le u$ for a real angle $\theta$. Let the evaluator’s
--   trigonometric output have cosine fields $(m_c,\sigma_c,r_c)$ and sine fields
--   $(m_s,\sigma_s,r_s)$, where each sign is $1$ or $-1$ according to its stored Boolean.
--   Then
--
--   $$\begin{aligned}
--   &|2^P\cos\theta-\sigma_c m_c|\le r_c,\quad
--   |2^P\sin\theta-\sigma_s m_s|\le r_s,\\
--   &m_c\le2^P,\qquad m_s\le2^P.
--   \end{aligned}$$
--
--   This validates the evaluator’s signed fixed-point trigonometric balls.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/Probes/ArbEconomics_Sound.lean#L778-L872

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
import Theorems.Thm_ArbEcon_phi_ball
import Theorems.Thm_ArbEcon_rot_cos_sin
import Theorems.Thm_ArbEcon_taylor_fixed
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

theorem ArbEcon.trig_sound (c : Cfg) (t : ℝ) (K : ℕ) (hv : Valid c t K) (θ : ℝ) (thlo thhi : ℕ)
    (hlo : (thlo : ℝ) ≤ θ * 2 ^ c.P) (hhi : θ * 2 ^ c.P ≤ thhi) :
    TrigOK c.P θ (trig c thlo thhi) := by sorry
