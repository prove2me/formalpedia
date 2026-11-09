-- Prove2me | Theorems.Thm_ExactLearningSeparation678_Randomized_fact_3_4
-- name    : ExactLearningSeparation678.Randomized.fact_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:23:29.636737+00:00
-- url     : https://prove2.me/theorems/088a4f5b-6441-4426-a54e-9222f152256f
-- title:
--   Fact 3.4 — injective parametrization and exact class size
-- statement:
--   For the full concept class $C_t$ of Definition 3.1, with $t=2^m$ and $m\ge2$, distinct parameter pairs $(P,s)$ define distinct Boolean functions. In particular,
--   $$|C_t|=t^{6(t+1)}.$$
--   All monic degree-$t$ polynomials are included, including $P(X)=X^t$.
--
--   This establishes that identifying the concept is equivalent to recovering its polynomial and slope, and supplies the class size for information lower bounds.
--
--   Differences from the source:
--   - encoding: t ≥ 4 is a power of two, with a fixed binary basis of F_(t^6) → m is a natural number at least 2, t = 2^m, F = GaloisField 2 (6m), with a chosen genuine binary basis and F₂-valued binary labels; reason: this realizes every permitted size and fixes the coordinate convention of Definition 3.1
-- source:
--   Srinivasan Arunachalam, Amin Shiraz Gilani, Nikhil S. Mande, STOC 2027 submission #678 (October 2026), Fact 3.4, p.19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/678.pdf

import Definitions.Def_ExactLearningSeparation678_Randomized_Construction

open Classical
set_option autoImplicit false

namespace ExactLearningSeparation678.Randomized

/-- Fact 3.4, p.19: injectivity is a conclusion, including when every lower coefficient is zero. -/
theorem fact_3_4 (m : Size) :
    Function.Injective (concept m) ∧ (conceptClass m).card = (t m) ^ (6 * (t m + 1)) := by sorry

end ExactLearningSeparation678.Randomized
