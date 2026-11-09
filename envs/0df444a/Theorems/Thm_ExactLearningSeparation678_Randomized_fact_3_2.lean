-- Prove2me | Theorems.Thm_ExactLearningSeparation678_Randomized_fact_3_2
-- name    : ExactLearningSeparation678.Randomized.fact_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:23:57.377973+00:00
-- url     : https://prove2.me/theorems/cef8bf54-c2ba-48f8-88be-c7460fc42270
-- title:
--   Fact 3.2 — truncation fibers and uniformity
-- statement:
--   Let $t=2^m$ with $m\ge2$, and fix the binary basis of $F=\mathbb F_{t^6}$ used in Definition 3.1. Every label $z\in\mathbb F_2^{2m}$ has exactly
--   $$|\operatorname{trunc}^{-1}(z)|=t^4$$
--   preimages. Consequently, the image of the uniform law on $F$ under truncation is the uniform law on $\mathbb F_2^{2m}$.
--
--   This gives the exact label frequencies used by the remaining polynomial facts and learning bounds.
--
--   Differences from the source:
--   - encoding: t ≥ 4 is a power of two, with a fixed binary basis of F_(t^6) → m is a natural number at least 2, t = 2^m, F = GaloisField 2 (6m), with a chosen genuine binary basis and F₂-valued binary labels; reason: this realizes every permitted size and fixes the coordinate convention of Definition 3.1
-- source:
--   Srinivasan Arunachalam, Amin Shiraz Gilani, Nikhil S. Mande, STOC 2027 submission #678 (October 2026), Fact 3.2, p.18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/678.pdf

import Definitions.Def_ExactLearningSeparation678_Randomized_Construction
import Definitions.Def_ExactLearningSeparation678_Randomized_Observations

open Classical
set_option autoImplicit false

namespace ExactLearningSeparation678.Randomized

/-- Fact 3.2, p.18: exact fibers and uniform pushforward, with the fixed genuine binary basis. -/
theorem fact_3_2 (m : Size) :
    (∀ z : Label m, (Finset.univ.filter (fun v => trunc m v = z)).card = (t m) ^ 4) ∧
    (PMF.uniformOfFintype (F m)).map (trunc m) = PMF.uniformOfFintype (Label m) := by sorry

end ExactLearningSeparation678.Randomized
