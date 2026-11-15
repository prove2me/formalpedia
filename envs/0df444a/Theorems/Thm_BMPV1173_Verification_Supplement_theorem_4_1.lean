-- Prove2me | Theorems.Thm_BMPV1173_Verification_Supplement_theorem_4_1
-- name    : BMPV1173.Verification.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:55:18.552204+00:00
-- url     : https://prove2.me/theorems/d28cd78c-a4d9-4d69-8bfa-63ab81271d93
-- title:
--   Theorem 4.1 — Promised Orthogonal Vectors upper bound
-- statement:
--   Fix arbitrary real constants $c_{\rm low}>0$ and $c_{\rm high}>0$, with no relation required between them. For each $n\ge2$, an input is an indexed list of $n$ Boolean vectors of dimension $n$, promised to have, for every pair of distinct positions, either at most $c_{\rm low}\log n$ or at least $c_{\rm high}n/\log n$ common ones. There is a bounded-error quantum algorithm deciding whether two distinct vectors are orthogonal with
--
--   $$\widetilde O(n^{17/12})$$
--
--   individual-bit queries. The bound's coefficient, logarithmic exponent and threshold may depend on the two fixed promise constants, but never on $n$ or the unknown input. Success is at least $2/3$ on every promised input. The empty or singleton case has no distinct pair and is handled without evaluating the promise thresholds. This is the promised-domain theorem, separate from the existing unrestricted OV result.
--
--   Differences from the source:
--   - encoding: indices in [n] and bounded-error individual-entry query complexity → Fin n and the published XOR-bit HasDecision/queryComplexity interfaces with success at least 2/3; reason: a bijective relabeling of all input bits; the operational model is unchanged
--   - encoding: soft-O notation → the published SoftDecisionBound with a fixed natural logarithmic exponent and coefficient before n; reason: suppresses only polylogarithmic factors and retains all input instances
--   - encoding: the promise uses n/log n and distinct positions → PromisedOV branches to the unrestricted domain when n<2, and uses the source intersection inequalities otherwise; reason: the smaller lists have no distinct pair, so their promise is vacuous and their OV answer is false; the branch avoids undefined source logarithmic thresholds
--   - encoding: the promise thresholds use log n with fixed positive c_low and c_high → the thresholds use the natural logarithm Real.log; reason: any fixed logarithm base above one rescales the two arbitrary positive promise constants inversely, preserving exactly the same promised instances
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, Theorem 4.1, printed p.21 = PDF p.21.

import Definitions.Def_BMPV1173_Verification_Supplement_Problems

namespace BMPV1173.Verification.Supplement

/-- Theorem 4.1, printed/PDF p.21, with every fixed positive promise pair. -/
theorem theorem_4_1 (cLow cHigh : ℝ) (hLow : 0 < cLow) (hHigh : 0 < cHigh) :
    SoftDecisionBound MatrixIndex (PromisedOV cLow cHigh)
      (fun _ => ov) (17 / 12 : ℝ) := by sorry

end BMPV1173.Verification.Supplement
