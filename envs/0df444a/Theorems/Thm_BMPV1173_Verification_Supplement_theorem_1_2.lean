-- Prove2me | Theorems.Thm_BMPV1173_Verification_Supplement_theorem_1_2
-- name    : BMPV1173.Verification.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:52:33.569981+00:00
-- url     : https://prove2.me/theorems/db8ba327-f8a0-4abb-82df-7d138a003320
-- title:
--   Theorem 1.2 — Boolean verification and self-product lower bounds
-- statement:
--   Let $A,B,C$ be arbitrary Boolean $n\times n$ matrices with individual-entry oracle access. Boolean product verification has the ordinary lower bound
--
--   $$Q(\mathrm{BMPV}_n)=\Omega(n^{5/4}).$$
--
--   The same lower bound holds when $B=A^{\mathsf T}$ and $C=J_n$, with the unknown oracle consisting only of $A$. Thus the restricted self-product test already has the stated difficulty. All circuits must succeed with probability at least $2/3$ on every input, and the coefficients and eventual thresholds are independent of $n$ and the input.
--
--   Differences from the source:
--   - encoding: indices in [n] and bounded-error individual-entry query complexity → Fin n and the published XOR-bit HasDecision/queryComplexity interfaces with success at least 2/3; reason: a bijective relabeling of all input bits; the operational model is unchanged
--   - encoding: ordinary O and Omega notation → existential positive coefficients and dimension thresholds before n; upper bounds supply circuits and lower bounds quantify every successful circuit; reason: expands the asymptotic notation without logarithmic losses or instance-dependent constants
--   - encoding: the lower bound holds even when B=A transpose and C=J_n → a second lower-bound clause for bmpv evaluated on the published (X,X transpose,J_n) map, with X as the sole oracle; reason: makes the immediately following restriction explicit and retains the unrestricted clause
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, Theorem 1.2, printed p.3 = PDF p.3.

import Definitions.Def_BMPV1173_Verification_Supplement_Asymptotics
import Definitions.Def_BMPV1173_Verification_Supplement_Problems

namespace BMPV1173.Verification.Supplement

/-- Theorem 1.2 and the restriction stated immediately below it, printed/PDF p.3. -/
theorem theorem_1_2 :
    OrdinaryDecisionLower VerificationIndex (fun _ => Set.univ) (fun _ => bmpv)
      (powerRate (5 / 4 : ℝ)) 2 ∧
    OrdinaryDecisionLower MatrixIndex (fun _ => Set.univ) (fun _ => selfProduct)
      (powerRate (5 / 4 : ℝ)) 2 := by sorry

end BMPV1173.Verification.Supplement
