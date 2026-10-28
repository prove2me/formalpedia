-- Prove2me | Theorems.Thm_ArbEcon_Off_ampl_sound
-- name    : ArbEcon.Off.ampl_sound
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:46:01.637781+00:00
-- url     : https://prove2.me/theorems/6cfce184-7399-4829-b7bb-708f2be5924b
-- title:
--   Rational enclosure for a power amplitude
-- statement:
--   Let configurations $c,o$ have $c.\mathrm{one}=2^{c.P}$ and
--   $o.\mathrm{oneQ}=2^{o.qc.P}$, with $o.q\ge1$. For $m\ge1$ and natural
--   $g_{\rm prev}$, let $(L,H)$ be the two bound components returned by the
--   defined $\operatorname{ampl}(c,o,m,g_{\rm prev})$. Then
--   $$L\le2^{c.P}m^{-(o.a-o.b)/o.q}\le H.$$
--   The exponent is evaluated in the real numbers; the bounds are integer data cast
--   to reals.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/EMZetaOfflineSound.lean#L173-L242

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineEval
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSound
import Definitions.Def_ArdaRS_Arithmetic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.IntervalCases
/-  EMZetaOfflineSound.lean -- soundness of the off-line Nat-only evaluator (EMZetaOfflineEval).

    Every function of `EMZetaOfflineEval` produces a TRUE enclosure:
      * `imul_sound`     : the product `x · v` of a nonnegative bracket and a term ball;
      * `ampl_sound`     : the validated Newton root brackets `2^P m^(-σ)`, `σ = (a - b)/q`
                           (for ANY Newton output: the two kernel comparisons decide the bracket);
      * `termTB_sound`   : the term ball of `m^(-s) = m^(-σ)(cos θ - i sin θ)`, `θ = t log m`;
      * `addChain_sound` : accumulator `k` receives `(log m)^k m^(-s)`;
      * `stepO_sound`, `runO_sound`, `chunkO_sound` : the loop invariant `InvO` (log bracket and
                           the `p + 1` complex balls of `Σ_{m ≤ n} (log m)^k m^(-s)`).
    The log increment and the cos/sin kernels are `ArbEcon.logInc`/`ArbEcon.trig`, whose soundness
    (`ArbEcon.logInc_bound`, `ArbEcon.trig_sound`) is reused unchanged.

    conjecture1_proved = False.  Finite interval arithmetic; nothing here is about RH.
-/



open Real Finset

section
namespace ArbEcon
end ArbEcon
open ArbEcon

section
namespace ArbEcon.Off
end ArbEcon.Off
open ArbEcon.Off



/-! ## A. Specifications. -/















/-! ## B. The bracket-times-ball product. -/



/-! ## C. Term balls, accumulation, the log chain. -/







/-! ## D. The validated amplitude bracket. -/

theorem ArbEcon.Off.ampl_sound (c : Cfg) (o : OCfg) (hone : c.one = 2 ^ c.P) (hQ : o.oneQ = 2 ^ (o.q * c.P))
    (hq : 1 ≤ o.q) (m gprev : ℕ) (hm : 1 ≤ m) :
    ((ampl c o m gprev).2.1 : ℝ) ≤ (m : ℝ) ^ (-(((o.a : ℝ) - o.b) / o.q)) * 2 ^ c.P ∧
    (m : ℝ) ^ (-(((o.a : ℝ) - o.b) / o.q)) * 2 ^ c.P ≤ ((ampl c o m gprev).2.2 : ℝ) := by sorry
