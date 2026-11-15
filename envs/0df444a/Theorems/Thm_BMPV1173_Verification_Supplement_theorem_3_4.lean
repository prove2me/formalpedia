-- Prove2me | Theorems.Thm_BMPV1173_Verification_Supplement_theorem_3_4
-- name    : BMPV1173.Verification.Supplement.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:54:08.204664+00:00
-- url     : https://prove2.me/theorems/00332499-aa79-4acb-8c7d-2b94e4036d9c
-- title:
--   Theorem 3.4 — Single-list Orthogonal Vectors lower bound
-- statement:
--   For an indexed list of $n$ Boolean vectors of dimension $n$, Orthogonal Vectors accepts when two distinct positions have disjoint supports. Equal bit strings at different positions are permitted. Under individual-bit oracle access, the ordinary lower bound is
--
--   $$Q(\mathrm{OV}_n)=\Omega(n^{5/4}),\qquad n\ge2.$$
--
--   This quantifies over every bounded-error algorithm for the entire input domain. It supplies the lower-bound counterpart to the existing general OV upper bound without adding a promise or switching to whole-vector queries.
--
--   Differences from the source:
--   - encoding: indices in [n] and bounded-error individual-entry query complexity → Fin n and the published XOR-bit HasDecision/queryComplexity interfaces with success at least 2/3; reason: a bijective relabeling of all input bits; the operational model is unchanged
--   - encoding: ordinary O and Omega notation → existential positive coefficients and dimension thresholds before n; upper bounds supply circuits and lower bounds quantify every successful circuit; reason: expands the asymptotic notation without logarithmic losses or instance-dependent constants
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, Theorem 3.4, printed p.18 = PDF p.18.

import Definitions.Def_BMPV1173_Verification_Supplement_Asymptotics

namespace BMPV1173.Verification.Supplement

/-- Theorem 3.4, printed/PDF p.18, for the published single-list bit oracle. -/
theorem theorem_3_4 :
    OrdinaryDecisionLower MatrixIndex (fun _ => Set.univ) (fun _ => ov)
      (powerRate (5 / 4 : ℝ)) 2 := by sorry

end BMPV1173.Verification.Supplement
