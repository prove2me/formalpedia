-- Prove2me | Theorems.Thm_ErlerGross_alternating_exp_hasSum_cosine_formula
-- name    : ErlerGross.alternating_exp_hasSum_cosine_formula
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-09-26T12:45:35.171766+00:00
-- url     : https://prove2.me/theorems/cc1e5374-9298-472e-bc7d-916cced46892
-- title:
--   HasSum form of the alternating secant partial-fraction expansion
-- statement:
--   For complex $a,b$ satisfying $|\operatorname{Re}a|<\operatorname{Re}b$, the alternating partial-fraction series converges to
--
--   $$\sum_{n=0}^\infty (-1)^n\left(\frac{1}{(2n+1)b-a}+\frac{1}{(2n+1)b+a}\right)=\frac{\pi}{2b\cos(\pi a/(2b))}.$$
--
--   The HasSum statement records both convergence and the value, and directly implies the corresponding tsum identity.
-- source:
--   Erler and Gross, Locality, Causality, and an Initial Value Formulation for Open String Field Theory, https://arxiv.org/abs/hep-th/0406199, Appendix B, p. 45; HasSum strengthening of the alternating partial-fraction identity

import Mathlib
import Definitions.Def_ErlerGross_defs
open Real Filter Topology MeasureTheory

namespace ErlerGross

theorem alternating_exp_hasSum_cosine_formula (a b : Complex)
    (hab : |a.re| < b.re) :
    HasSum (fun n : Nat => (-1 : Complex)^n *
      (1 / (((2 * n + 1 : Nat) : Complex) * b - a) +
       1 / (((2 * n + 1 : Nat) : Complex) * b + a)))
      ((Real.pi : Complex) / (2 * b) * (1 / Complex.cos ((Real.pi : Complex) * a / (2 * b)))) := by
  sorry

end ErlerGross
