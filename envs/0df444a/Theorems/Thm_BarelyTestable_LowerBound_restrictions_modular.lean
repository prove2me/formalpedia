-- Prove2me | Theorems.Thm_BarelyTestable_LowerBound_restrictions_modular
-- name    : BarelyTestable.LowerBound.restrictions_modular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T12:21:25.383509+00:00
-- url     : https://prove2.me/theorems/5f6d4d42-bc36-4be9-a4b8-c72b906c00c6
-- title:
--   Lemma 2.3 — restrictions and modular shifts
-- statement:
--   Let $f$ be any real submodular function on a Boolean cube. Fix any set $R$ of free coordinates and any assignment $Z$ outside it. Let $h$ be any modular function, including one with a nonzero constant term. Then both assertions hold:
--
--   $$f|_{R,Z}\text{ is submodular},\qquad f+h\text{ is submodular}.$$
--
--   The first conclusion ranges over every coordinate restriction, including no free coordinates and all free coordinates. These closure facts justify working within individual slices.
--
--   Differences from the source:
--   - encoding: Boolean vectors with coordinates numbered from 1 → finite subsets of Fin n, numbered from 0; reason: the incidence-vector bijection preserves every vertex, union, intersection and coordinate square
--   - encoding: fix any set of coordinates → restriction f R Z evaluates at (Z minus R) union T; reason: Z is an arbitrary assignment and the free set T has the subtype R as its coordinate type
-- source:
--   Diptaksho Palit, Yuichi Yoshida, STOC 2027 submission #722 (October 2026), Lemma 2.3, p. 10 (printed = PDF page); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/722.pdf; PDF SHA256 a095e6ef801edf5b0ce3967efca977e04b7a0b4374e874116509d73837bd14f3

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Cube

set_option autoImplicit false

namespace BarelyTestable.LowerBound

open NonmonotoneSubmod.Shared MeasureTheory

/-- Lemma 2.3, p.10: restrictions and arbitrary modular shifts, including constants. -/
theorem restrictions_modular {n : ℕ} (f : Oracle (Fin n)) (hf : Submodular f) :
    (∀ R Z : Cube (Fin n), Submodular (restriction f R Z)) ∧
    (∀ h : Oracle (Fin n), Modular h → Submodular (fun S => f S + h S)) := by sorry

end BarelyTestable.LowerBound
