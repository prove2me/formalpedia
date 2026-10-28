-- Prove2me | Theorems.Thm_DIntvProd_DIntv_add_sound
-- name    : DIntvProd.DIntv.add_sound
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:41:12.15585+00:00
-- url     : https://prove2.me/theorems/31213371-cd64-4502-b8b2-0a85427d5abc
-- title:
--   Soundness of dyadic interval addition
-- statement:
--   Let $I,J$ be dyadic intervals with the same exponent, and let $x\in I$ and
--   $y\in J$ be real numbers. If $I\oplus J$ is their defined dyadic interval sum, then
--
--   $$x+y\in I\oplus J.$$
--
--   This justifies interval addition in the certified arithmetic.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/DIntvDef.lean#L61-L80

import Definitions.Def_ArdaRS_Dyadic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
/-  DIntvDef.lean -- production-intended dyadic interval definitions + mem-soundness.

    This is the cleaner, production sibling of `Spike/DIntvMini.lean`.  It carries the
    SAME computable ops (add, mul, neg) and, crucially, PROVES that they are sound with
    respect to the real interval they denote:

        I.memR x  :=  (I.lo : ℝ) * 2^I.e ≤ x ∧ x ≤ (I.hi : ℝ) * 2^I.e

    We prove `add_sound` and `mul_sound` ONLY (the A0 remit): if `x ∈ I` and `y ∈ J`
    then `x + y ∈ I.add J` and `x * y ∈ I.mul J`.  These validate the Real-bridging
    proof style that the full A1 correctness surface will scale up.

    Design note for A1: to keep the soundness proofs clean we store BOTH endpoints at a
    COMMON exponent (add aligns to the shared exponent; mul adds exponents).  `roundTo`
    (outward widening) is a separate, monotone op whose soundness is a one-liner from
    `add`/`mul` monotonicity and is deferred to A1.

    conjecture1_proved = False.  This is finite interval arithmetic, not a proof of RH.
-/



section
namespace DIntvProd
end DIntvProd
open DIntvProd



section
namespace DIntvProd.DIntv
end DIntvProd.DIntv
open DIntvProd.DIntv









/-! ### Soundness -/

theorem DIntvProd.DIntv.add_sound {x y : ℝ} {I J : DIntv} (h : I.e = J.e)
    (hx : memR x I) (hy : memR y J) : memR (x + y) (add I J h) := by sorry
