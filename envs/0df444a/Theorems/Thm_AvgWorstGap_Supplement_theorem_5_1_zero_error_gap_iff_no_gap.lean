-- Prove2me | Theorems.Thm_AvgWorstGap_Supplement_theorem_5_1_zero_error_gap_iff_no_gap
-- name    : AvgWorstGap.Supplement.theorem_5_1_zero_error_gap_iff_no_gap
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:10:14.578082+00:00
-- url     : https://prove2.me/theorems/c2c25315-be6c-4489-b4f8-602fb38f27c4
-- title:
--   Theorem 5.1 — zero-error average case: "$\mathrm{Gap}\text{-}\mathrm{MINpKT}^{\mathsf{PH}}\in\mathsf{AvgBPP}$" iff "$\mathrm{MINpKT}^{\mathsf{PH}}\in\mathsf{AvgBPP}$"
-- statement:
--   $$\text{“}\mathrm{Gap}\text{-}\mathrm{MINpKT}^{\mathsf{PH}}\in\mathsf{AvgBPP}\text{”}\iff\text{“}\mathrm{MINpKT}^{\mathsf{PH}}\in\mathsf{AvgBPP}\text{”}.$$
--
--   Both sides are average-case statements with zero error in the sense of Definition 2.20. The left side says: for every $O\in\mathsf{PH}$ there is a polynomial $\rho$ such that, for every polynomial-time samplable family $\{D_n\}$ with $D_n$ supported on $\{0,1\}^n$, one probabilistic polynomial-time algorithm $A$ satisfies, for all $n,s,t,a,b$ and $k\ge1$,
--
--   1. with probability at least $1-1/k$ over $x\sim D_n$, $A(-;1^k)$ decides $\mathrm{Gap}_\rho\text{-}\mathrm{MINpKT}^O$ on $(x,1^s,1^t,1^a,1^b)$ with probability more than $3/5$;
--   2. for every $x$ in the support of $D_n$, with probability at least $4/5$, $A(-;1^k)$ either decides the problem on $(x,1^s,1^t,1^a,1^b)$ or outputs $\bot$.
--
--   The right side is the same with the no-gap problem $\mathrm{MINpKT}^O$ (YES: $\mathrm{pK}^{t,O}_{b/a}(x)\le s$; NO: $\mathrm{pK}^{t,O}_{(b-1)/a}(x)>s$) in place of the gap problem.
--
--   In the zero-error average-case setting, the polynomial time gap of the standard problem therefore costs nothing: estimating $\mathrm{pK}^t$ with a gap is as hard on average as deciding it exactly up to the threshold.
--
--   Differences from the source:
--   - reading: instances (x, 1^s, 1^t, 1^a, 1^b) with any a, b → an instance is in YES or NO only if 1 ≤ b ≤ a; reason: b/a and (b − 1)/a must lie in [0, 1], the domain of Def. 2.2 (the guard of the published Gap/Mild-Gap-MINpKT)
--   - reading: "straightforward to extend the above definitions to … MINpKT^PH" (p.19) → Def. 2.19 / 2.20 with MINpKT^O in place of Gap_ρ-MINpKT^O, for every O ∈ PH, all other quantifiers and thresholds unchanged; reason: the paper gives no separate definition; this is the direct substitution
--   - reading: heuristic-scheme conditions for every n, k ∈ ℕ → for every n and every k ≥ 1; reason: 1 − 1/k is undefined at k = 0
--   - reading: PSAMP samplers for every n ≥ 1, D_0 unconstrained → a sampler for every n ∈ ℕ (the published InPSAMP); reason: the schemes quantify every n ∈ ℕ, so an unconstrained D_0 of full support would force L to be decidable in the worst case for every (L, D) in the average-case class
--   - encoding: a polynomial ρ → ρ ∈ Polynomial ℕ, evaluated at n; reason: NO shrinks as ρ grows and every polynomial ℕ → ℕ is dominated by one with natural coefficients, so the existential is the same
--   - encoding: multi-tape machines with a fixed standard encoding (details unspecified) → the published Machine and the published encoding code; reason: the paper fixes none of these details
--   - encoding: tuples (x, 1^s, 1^t, …) and (z; 1^k) → the self-delimiting tupleEnc; reason: the paper fixes no encoding
--   - encoding: minima over ℕ, log, comparisons with s + log ρ → values in ℕ∞ (⊤ for an empty minimum), Real.logb 2, comparisons in EReal; reason: Lean convention; same instances
--   - encoding: distribution families and Pr_{x∼D_n} → PMF (List Bool) and its outer measure; reason: Lean convention; same distributions
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Theorem 5.1, p.35 (proof pp.35–36)

import Mathlib
import Definitions.Def_AvgWorstGap_Supplement_EasyOnAvg

namespace AvgWorstGap.Supplement

open NKtLB

/-- **Theorem 5.1** (Goldberg, Hu, Lu, Lyu, Oliveira, *The Gap Between Average-Case and Worst-Case Complexity*,
arXiv:2610.19162, version of October 30, 2026, p.35): "The following holds:
“`Gap-MINpKT^PH ∈ AvgBPP`” ⇐⇒ “`MINpKT^PH ∈ AvgBPP`”."

**Formalization Note.** Both sides in the sense of Def. 2.20 (p.19): for every `O ∈ PH` and every
polynomial-time samplable family supported over `{0,1}^n` there is one PPT algorithm with the
`> 3/5`, `≥ 1 − 1/k` and `≥ 4/5` guarantees for all `n, s, t, a, b` and `k ≥ 1`; on the left
for `Gap_ρ-MINpKT^O` with some polynomial `ρ`, on the right for `MINpKT^O`. -/
theorem theorem_5_1_zero_error_gap_iff_no_gap : GapPHInAvgBPP ↔ MINpKTPHInAvgBPP := by sorry

end AvgWorstGap.Supplement
