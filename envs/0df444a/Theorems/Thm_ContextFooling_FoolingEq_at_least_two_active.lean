-- Prove2me | Theorems.Thm_ContextFooling_FoolingEq_at_least_two_active
-- name    : ContextFooling.FoolingEq.at_least_two_active
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:44.334028+00:00
-- url     : https://prove2.me/theorems/d70cbf45-d553-4a27-af56-9e60dd435a0f
-- title:
--   Appendix, p. 34 (PDF 35) — in every competitive equilibrium at least two firms have positive demand
-- statement:
--   Under the standing assumptions, fix either context technology, store-wide or product-specific. In every competitive equilibrium $(M^k)_{k\le K}$, at least two firms have strictly positive demand:
--
--   $$\#\{k:\ \text{firm }k\text{ has positive demand}\}\ \ge\ 2.$$
--
--   If at most one firm were active, some firm would face only rivals offering the empty menu and could deviate to a positive margin with positive demand. This is the market part of every characterization in the paper.
-- source:
--   Apffelstaedt & Mechtenberg, Competition for Context-Sensitive Consumers, MPRA Paper No. 99509 (version of November 2016; published in Management Science, doi:10.1287/mnsc.2020.3675), p. 34 (PDF 35), Appendix introduction

import Mathlib
import Definitions.Def_ContextFooling_FoolingEq_Model

namespace ContextFooling.FoolingEq

/-- Appendix, p. 34: in every competitive equilibrium, under either context technology, at least
two firms have strictly positive demand. -/
theorem at_least_two_active (P : Params) (hP : P.Standing) (Tech : Finset Product → Prop)
    (hTech : Tech = StoreWide ∨ Tech = ProductSpecific) (σ : Profile P)
    (hσ : IsCompEq P Tech σ) :
    2 ≤ (active P σ).card := by sorry

end ContextFooling.FoolingEq
