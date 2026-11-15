-- Prove2me | Theorems.Thm_BMPV1173_Verification_Supplement_theorem_5_2
-- name    : BMPV1173.Verification.Supplement.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:55:51.689639+00:00
-- url     : https://prove2.me/theorems/72817566-b941-49dd-9e4a-328f33a39566
-- title:
--   Theorem 5.2 — Full row-search query chain
-- statement:
--   For arbitrary Boolean $n\times n$ matrices $A,B$ and a Boolean target $v\in\{0,1\}^n$, let $\mathrm{BMPRS}_n$ ask whether some row of $A\mathbin\bullet B$ equals $v$. Let $\mathrm{BMPRS}^1_n$ fix the target to $1^n$ and access only the two matrices. Under individual-entry queries and success at least $2/3$,
--
--   $$\Omega\!\left(\frac{n^{3/2}}{\sqrt{\log n}}\right)\le Q(\mathrm{BMPRS}^1_n)\le Q(\mathrm{BMPRS}_n)=O(n^{3/2}),\qquad n\ge8.$$
--
--   The middle comparison holds for every $n\ge8$. Both asymptotic coefficients are uniform before $n$, and the upper bound is ordinary $O$ for every target vector, including the cost of querying it. This retains the whole source chain and the square root of the logarithm in its lower bound.
--
--   Differences from the source:
--   - encoding: indices in [n] and bounded-error individual-entry query complexity → Fin n and the published XOR-bit HasDecision/queryComplexity interfaces with success at least 2/3; reason: a bijective relabeling of all input bits; the operational model is unchanged
--   - encoding: ordinary O and Omega notation → existential positive coefficients and dimension thresholds before n; upper bounds supply circuits and lower bounds quantify every successful circuit; reason: expands the asymptotic notation without logarithmic losses or instance-dependent constants
--   - encoding: entry access to A,B,v; only A,B for the all-ones restriction → a disjoint sum of two matrix-index copies and vector indices; the restriction removes vector indices and inserts constant true answers; reason: all and only source input bits are unknown; the existing Boolean product is reused through a lossless adapter
--   - encoding: n^(3/2)/sqrt(log n), with an unspecified fixed logarithm base → rowLowerRate uses Real.log, the natural logarithm; reason: changing a fixed logarithm base above one multiplies the rate by a positive constant absorbed into the existential lower-bound coefficient
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, Theorem 5.2, printed p.34 = PDF p.34.

import Definitions.Def_BMPV1173_Verification_Supplement_Asymptotics
import Definitions.Def_BMPV1173_Verification_Supplement_RowSearch

namespace BMPV1173.Verification.Supplement

/-- Theorem 5.2, printed/PDF p.34: the entire chain, with an ordinary O upper bound. -/
theorem theorem_5_2 :
    OrdinaryDecisionLower TwoMatrixIndex (fun _ => Set.univ) (fun _ => bmprsOne)
      rowLowerRate 8 ∧
    (∀ n : ℕ, 8 ≤ n → qBMPRSOne n ≤ qBMPRS n) ∧
    OrdinaryDecisionUpper RowSearchIndex (fun _ => Set.univ) (fun _ => bmprs)
      (powerRate (3 / 2 : ℝ)) 8 := by sorry

end BMPV1173.Verification.Supplement
