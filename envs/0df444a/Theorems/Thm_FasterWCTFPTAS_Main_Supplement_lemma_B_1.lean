-- Prove2me | Theorems.Thm_FasterWCTFPTAS_Main_Supplement_lemma_B_1
-- name    : FasterWCTFPTAS.Main.Supplement.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:10:31.87032+00:00
-- url     : https://prove2.me/theorems/e0de000f-6117-4d6d-82e1-37bf14a8cd2a
-- title:
--   Lemma B.1 — polynomial scheduling gap reduction
-- statement:
--   For every fixed $m\ge2$, there are one deterministic admissible program and constants $C>0,d\in\mathbb N$, depending only on $m$. On every size-$n$ Grouped $m$-way Partition instance $I$ with bound $W$, the program either outputs $[0]$ and correctly certifies that $I$ is No, or constructs an instance $I'$ on exactly $n$ jobs and numbers $\Lambda,\lambda>0$ such that
--
--   $$\frac{\Lambda}{\lambda}\le Cn^dW^2,\qquad
--   I\in\mathrm{Yes}\Rightarrow\operatorname{OPT}(I')\le\Lambda,\qquad
--   I\in\mathrm{No}\Rightarrow\operatorname{OPT}(I')\ge\Lambda+\lambda.$$
--
--   The constructed processing times are positive and weights nonnegative. On either branch it halts within $C(n+1+\log_2(W+1))^d$ actual instructions. Output on the construction branch is $[1,\Lambda,\lambda,p_1,\ldots,p_n,w_1,\ldots,w_n]$. The constant and degree are uniform over $s,q,W$ and all item values. This is the complete gap reduction used for Theorem 1.2, including all three numbered conclusions and the optional early No determination.
--
--   Differences from the source:
--   - reading: the deterministic polynomial-time algorithm has no named machine → the program uses the published deterministic real RAM; reason: retains the adopted machine convention shared by the base mission and the conditional bounds
--   - encoding: polynomial time and Λ/λ ≤ n^{O(1)} W² → uniform C > 0 and d in N bound time by C(n+1+log₂(W+1))^d and ratio by C n^d W²; reason: makes binary input length explicit and preserves exponent 2 on W; enlarging C and d bounds both quantities
--   - encoding: finite groups, subsets, and one-based indices → zero-based Fin arrays and position selections with explicit fixed input/output layouts; reason: enumerates the same objects; row injectivity is required only for sets and duplicates remain distinct in multisets
-- source:
--   Karl Bringmann, Anita Dürr, Karol Węgrzycki, A Faster FPTAS for Weighted Completion Time Scheduling, STOC 2027 submission #1072 (October 2026), p.27 (PDF p.28), Lemma B.1.

import Definitions.Def_FasterWCTFPTAS_Main_Supplement_SchedulingPrograms

set_option autoImplicit false

namespace FasterWCTFPTAS.Main.Supplement

/-- Lemma B.1, printed p.27 (PDF 28): support for Theorem 1.2, all three clauses
and the early No branch, with a polynomial binary-input runtime and exact W² ratio. -/
theorem lemma_B_1 :
    ∀ m : ℕ, 2 ≤ m → HasGapReduction m := by sorry

end FasterWCTFPTAS.Main.Supplement
