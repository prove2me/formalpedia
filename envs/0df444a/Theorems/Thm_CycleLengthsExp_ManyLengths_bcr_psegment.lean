-- Prove2me | Theorems.Thm_CycleLengthsExp_ManyLengths_bcr_psegment
-- name    : CycleLengthsExp.ManyLengths.bcr_psegment
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-18T20:05:41.798451+00:00
-- url     : https://prove2.me/theorems/f14d1db8-7214-44a3-a47d-b39dfaa8fa0d
-- title:
--   P-segment glue (Friedman-Krivelevich p. 14): segment function on a path with index-distance length formula + idxOf injectivity
-- statement:
--   P-segment glue (Friedman-Krivelevich, p. 14, proof of Theorem 2).
--
--   Setup: P is a path in G from u to v.
--
--   Conclusion: there is a segment function seg assigning to every pair
--   a, b in P.support a walk seg(a, b) in G from a to b, such that:
--   (i) every segment is a path; (ii) every segment's support is contained in
--   P.support; (iii) the segment's length is the index distance
--   |idxOf(b) - idxOf(a)| along P (via the if on the order of the two
--   indices); and (iv) idxOf is injective on P.support.
--
--   Why: for a, b in P.support, if pos(a) <= pos(b) the segment is
--   (P.dropUntil a).takeUntil b, else the reverse direction. The length
--   formula follows from take_spec (takeUntil ++ dropUntil = whole) plus
--   support prefix/suffix lemmas (support_takeUntil_prefix_support,
--   support_dropUntil_suffix_support): for a path, support is nodup, so
--   P.support.idxOf(a) = (P.takeUntil a).length, and the segment's support is
--   the sublist from a to b, giving length = |idxOf(b) - idxOf(a)|. InjOn
--   idxOf on P.support is List.idxOf_inj plus nodup.
--
--   This is DEEP INPUT B of the decomposition of
--   CycleLengthsExp.ManyLengths.branch_cycles_repaired (parent, Open): the
--   assembly consumes seg and the length formula to build one cycle per
--   w in X3 as (P-segment w0 -> w) ++ (T-leg w -> w0), with the length
--   formula giving the cycle length A + segLen(w) and idxOf injectivity
--   giving InjOn segLen on X3.
-- source:
--   Friedman–Krivelevich, Cycle lengths in expanding graphs, arXiv:1912.11011v2, p. 14, proof of Theorem 2 (P-segment glue). DEEP INPUT B of the decomposition of CycleLengthsExp.ManyLengths.branch_cycles_repaired; see ~/workspace/p2m_harness/work/theorem_2/branch_cycles_repaired_decomp.lean (axiom bcr_psegment, extracted verbatim).

import Mathlib
import Definitions.Def_CycleLengthsExp_ManyLengths_Setting

namespace CycleLengthsExp.ManyLengths

/-- P-segment glue (Friedman–Krivelevich, p. 14, proof of Theorem 2).

Setup: `P` is a path in `G` from `u` to `v`.

Conclusion: there is a segment function `seg` assigning to every pair
`a, b ∈ P.support` a walk `seg a b` in `G` from `a` to `b`, such that:
(i) every segment is a path; (ii) every segment's support is contained in
`P.support`; (iii) the segment's length is the index distance
`|idxOf b - idxOf a|` along `P` (via the `if` on the order of the two
indices); and (iv) `idxOf` is injective on `P.support`.

Proof sketch: for `a, b ∈ P.support`, if `pos a ≤ pos b` the segment is
`(P.dropUntil a).takeUntil b`, else the reverse direction. The length
formula follows from `take_spec` (`takeUntil ++ dropUntil = whole`) +
support prefix/suffix lemmas (`support_takeUntil_prefix_support`,
`support_dropUntil_suffix_support`): for a path, support is nodup, so
`P.support.idxOf a = (P.takeUntil a).length`, and the segment's support is
the sublist from `a` to `b`, giving `length = |idxOf b - idxOf a|`. InjOn
`idxOf` on `P.support` is `List.idxOf_inj` + nodup.

This is DEEP INPUT B of the decomposition of
`CycleLengthsExp.ManyLengths.branch_cycles_repaired` (parent, Open): the
assembly consumes `seg` and the length formula to build one cycle per
`w ∈ X₃` as (P-segment `w₀ → w`) ++ (T-leg `w → w₀`), with the length
formula giving the cycle length `A + segLen w` and `idxOf` injectivity
giving `InjOn segLen X₃`. -/
theorem bcr_psegment (n : ℕ) (G : SimpleGraph (Fin n))
    (u v : Fin n) (P : G.Walk u v) (hPpath : P.IsPath) :
    ∃ (seg : ∀ (a b : Fin n), a ∈ P.support → b ∈ P.support → G.Walk a b),
      (∀ a b ha hb, (seg a b ha hb).IsPath) ∧
      (∀ a b ha hb, (seg a b ha hb).support ⊆ P.support) ∧
      (∀ a b ha hb, (seg a b ha hb).length =
        if P.support.idxOf a ≤ P.support.idxOf b then
          P.support.idxOf b - P.support.idxOf a else
          P.support.idxOf a - P.support.idxOf b) ∧
      (∀ a ∈ P.support, ∀ b ∈ P.support,
        P.support.idxOf a = P.support.idxOf b → a = b) := by
  sorry

end CycleLengthsExp.ManyLengths
