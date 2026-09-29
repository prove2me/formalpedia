-- Prove2me | Theorems.Thm_ErlerGross_alternating_exp_tsum_eq_cosine_formula
-- name    : ErlerGross.alternating_exp_tsum_eq_cosine_formula
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-26T10:10:18.726968+00:00
-- url     : https://prove2.me/theorems/1ff8f8d6-eacf-4cd0-952d-796f969e86f1
-- title:
--   Alternating exponential series for the complex secant
-- statement:
--   Let $a,b\in\mathbb C$ satisfy $|\operatorname{Re}a|<\operatorname{Re}b$. Then the alternating odd-lattice sum has the closed form
--
--   $$
--   \sum_{n=0}^\infty(-1)^n\left(\frac{1}{(2n+1)b-a}+\frac{1}{(2n+1)b+a}\right)
--   =\frac{\pi}{2b\cos\!\left(\frac{\pi a}{2b}\right)}.
--   $$
--
--   This partial-fraction identity gives the closed-form value appearing in the Erler–Gross integral formula.
-- source:
--   Erler and Gross, Locality, Causality, and an Initial Value Formulation for Open String Field Theory, https://arxiv.org/abs/hep-th/0406199, Appendix B, p. 45.; alternating partial-fraction form of the displayed integral identity.

import Mathlib
import Definitions.Def_ErlerGross_defs
open Real Filter Topology MeasureTheory

namespace ErlerGross

theorem alternating_exp_tsum_eq_cosine_formula (a b : ℂ)
    (hab : |a.re| < b.re) :
    ∑' n : ℕ, (-1 : ℂ)^n *
      (1 / (((2 * n + 1 : ℕ) : ℂ) * b - a) +
       1 / (((2 * n + 1 : ℕ) : ℂ) * b + a)) =
      (π : ℂ) / (2 * b) * (1 / Complex.cos (π * a / (2 * b))) := by
  sorry

end ErlerGross
