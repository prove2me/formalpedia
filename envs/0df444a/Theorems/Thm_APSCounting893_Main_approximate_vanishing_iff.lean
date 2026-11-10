-- Prove2me | Theorems.Thm_APSCounting893_Main_approximate_vanishing_iff
-- name    : APSCounting893.Main.approximate_vanishing_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:01:39.658208+00:00
-- url     : https://prove2.me/theorems/80504381-e9fb-4f67-9b3f-432831540ee8
-- title:
--   Theorem 3.11 — Approximate vanishing, closure and annihilators
-- statement:
--   For any polynomial tuple $F:\mathbb C^n\to\mathbb C^m$, let $\operatorname{AV}(F)$ consist of Puiseux assignments on which every output has positive valuation, and let $\operatorname{Ann}(F)$ be its substitution kernel. Then
--
--   $$\operatorname{AV}(F)\ne\varnothing\iff0\in\overline{F(\mathbb C^n)}\iff\forall P\in\operatorname{Ann}(F),\ P(0)=0.$$
--
--   Both equivalences are asserted separately. The closure and the unrestricted positive-denominator Puiseux union are essential; exact common zeros are not substituted for approximate vanishing.
--
--   Differences from the source:
--   - encoding: the field union of all Puiseux ramification denominators → witness coordinates in the union of the published ramified Laurent subfields inside Hahn series; reason: retains every denominator and the convention that the zero series has infinite valuation
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), Theorem 3.11, p. 13, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_Geometry

set_option autoImplicit false

namespace APSCounting893.Main

theorem approximate_vanishing_iff (n m : ℕ) (F : PolynomialMap ℂ n m) :
    ((approximateVanishing F).Nonempty ↔ hasAPS F) ∧
      (hasAPS F ↔ ∀ P ∈ annihilator F, MvPolynomial.eval (0 : Affine ℂ m) P = 0) := by sorry

end APSCounting893.Main
