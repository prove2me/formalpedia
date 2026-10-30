-- Prove2me | Theorems.Thm_BudgetFeasibleClockAuctions_SymmetricPostedPrice_mechanism5_logarithmic_approximation
-- name    : BudgetFeasibleClockAuctions.SymmetricPostedPrice.mechanism5_logarithmic_approximation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:34:46.448993+00:00
-- url     : https://prove2.me/theorems/a7bc7c0d-0150-480c-8029-bd5e2cc24e16
-- title:
--   Theorem 15 — logarithmic approximation (corrected: reserve return and proof bounds)
-- statement:
--   Let $N$ have $n$ bidders, let the public budget be $B$, let $0\le c_i\le B$ be their real costs, and choose any reserve $j\in N$. Bidders are processed in any public order. Acceptance includes equality. Use Mechanism 5 with the proof-consistent fallback acquisition, and write $(W,p)$ for its final winning set and offered-price record. Only $p_i$ for $i\in W$ is paid. A chosen reserve entails $n\ge1$ and affordability entails $B\ge0$; singleton and zero-budget instances remain included.
--
--   Let $v$ be symmetric submodular: there are $r_1\ge\cdots\ge r_n\ge0$ with $v(S)=\sum_{t=1}^{|S|}r_t$ for every subset $S$. A set $O\subseteq N$ is true-cost-feasible when $\sum_{i\in O}c_i\le B$; this benchmark includes the reserve.
--
--   For every such instance the computed output satisfies
--
--   $$\sum_{i\in W}p_i\le B,\qquad
--   v(O)\le(2+2\ln n)v(W)\quad\text{for every true-cost-feasible }O.$$
--
--   For $n\ge2$ it also satisfies
--
--   $$v(O)\le5\ln n\,v(W)\quad\text{for every true-cost-feasible }O.$$
--
--   Thus one absolute constant gives the source's $O(\log n)$ approximation, uniformly over budgets, costs, valuations, public orders and reserves. The factor $2+2\ln n$ is a numerical instantiation of that asymptotic theorem after correcting its proof, rather than the false sharper Case 2 factor. At $n=1$ the scan is empty and the reserve is acquired at $B$. At $B=0$ and $n\ge2$ all $n-1$ scanned bidders accept for zero payment. Zero values and ties remain included. This goal concerns the algorithm's computed output and the full true-cost benchmark, with no welfare or feasibility conclusion assumed in its data.
--
--   Differences from the source:
--   - correction: Mechanism 5 line 13 offers B to j but does not update W → insert j and pay its accepted fallback offer when the scan count is zero; reason: Case 1 explicitly returns j; n=4, B=1, all costs and marginals 1 give empty output under the literal code but OPT=1
--   - correction: opening payment display uses 1+1+1/2+...+1/(n-1) and concludes spending < B → k actual scan acceptances spend B(1+H_(k-1))/(2 ln n), zero when k=0; all prefixes and the final output spend at most B, with strict scan spending only when n≥2 and B>0; reason: n=3, B=1, zero costs and unit marginals give printed spending 1.137799>B but actual spending 0.910239; the fallback spends exactly B and B=0 gives equality
--   - correction: Case 1 equates OPT/v(M) with an upper bound and concludes a strict ratio bound → v(O)≤(1+2 ln n)v(W) for every true-cost-feasible O, without dividing by values; reason: zero marginals make the ratio undefined; n=1, B=1, cost 1 and marginal 1 give OPT=v(W)=1, refuting strictness; the displayed equality is only an upper bound
--   - correction: Case 2 omits the unqueried reserve and concludes factor 1+2 ln n → v(O)≤v(W)+(2k ln n+1)r_k≤(1+2 ln n+1/k)v(W)≤(2+2 ln n)v(W); reason: n=4, B=1, unit marginals, main costs (0,2/5,2/5) and reserve cost 0 give k=1, v(W)=1, OPT=4>1+2 ln 4; the added marginal counts precisely the reserve
--   - correction: Case 2 compares earlier offers strictly and uses equalities and strict ratios divided by r_k and v(W) → earlier offers are weakly larger; the welfare chain consists of non-strict cross-multiplied inequalities with division only by k≥1; reason: the a=0 and a=1 offers coincide; all-zero marginals give r_k=v(W)=0 on valid instances, so division by values is not defined in the source
--   - reading: Mechanism 5 input calls the valuation additive → the full symmetric submodular class, including nonconstant marginals; reason: the heading, section definition, Theorem 15 and its proof specify this class
--   - reading: section B.2 writes S ⊆ 2^N → S is a subset of N; reason: the declared domain v:2^N→ℝ≥0 and section 2 determine the intended type
--   - reading: Case 1 sums to the generally nonintegral upper endpoint 2 ln n+1 → a welfare bound for every actual finite cost-feasible subset; reason: the source gives no floor convention or extension of the n marginals; no such convention is required
--   - reading: Case 2 sums to the generally nonintegral endpoint 2k ln n+k → a tail bound for actual finite feasible subsets with k equal to the computed scan count; reason: only existing marginals are accessed; the reserve correction applies to the cardinality bound
--   - reading: Case 1 says each agent rejects the initial offer → the zero-count premise concerns only scanned bidders; the affordable reserve accepts B; reason: j is set aside from the loop and is not subject to its rejection lower bound
--   - encoding: an arbitrarily ordered nonempty finite bidder set and arbitrary reserve → Fin n in increasing label order, universally quantified costs and reserve j:Fin n; reason: every public order is represented by relabeling; j entails n≥1 and 0≤c_j≤B entails B≥0, without excluding n=1 or B=0
--   - encoding: nonnegative v(S)=sum of the first |S| decreasing nonnegative marginals r_1,...,r_n → the published IsSymmetricSubmodular n v predicate on real-valued finite-set functions, with r(t) storing r_(t+1); reason: the predicate supplies exactly the source representation; indices ≥n are irrelevant and zero marginals and ties remain included
--   - encoding: pay the accepted offer to every winner → sum the published offered-price record only over computed winners; reason: the record also contains rejected offers; actual payment is that record on W and zero outside W
--   - encoding: OPT is the maximum value of a true-cost-feasible subset of all bidders → the welfare inequality holds for every O⊆Fin n with sum of c_i over O at most B, including O containing j; reason: the family is finite and nonempty because B≥0; this is equivalent to the attained optimal-value bound and assumes no optimality certificate
--   - encoding: Theorem 15 states O(log n) without a numerical constant → the absolute factor 2+2 ln n for every source-valid n, and 5 ln n whenever n≥2; reason: this instantiates the same asymptotic result after correcting the false intermediate bound; the constant 5 is fixed before every instance and 2+2 ln n≤5 ln n for n≥2
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, §B.2, Theorem 15 and Mechanism 5, printed p. 27, PDF p. 28; proof opening and Cases 1–2, printed pp. 27–28, PDF pp. 28–29; standing model §2, printed p. 5, PDF p. 6; symmetric valuation §B.2, printed p. 25, PDF p. 26

import Mathlib
import Definitions.Def_BudgetClock_PostedSym_Setting
import Theorems.Thm_BudgetClock_PostedSym_theorem_15

open BudgetClock.PostedSym

namespace BudgetFeasibleClockAuctions.SymmetricPostedPrice

/-- arXiv:2107.09239v2, Theorem 15, printed p. 27 / PDF p. 28; proof pp. 27-28 / PDF 28-29.
Corrected: the fallback acquires the accepting reserve. The explicit absolute factor counts
the reserve in the benchmark and replaces the proof's false sharper intermediate bound.
All source-valid instances, including n = 1, B = 0, ties and zero marginals, remain included. -/
theorem mechanism5_logarithmic_approximation (n : ℕ) (v : Finset (Fin n) → ℝ)
    (hv : IsSymmetricSubmodular n v) (B : ℝ) (c : Fin n → ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (hcB : ∀ i, c i ≤ B) (j : Fin n) :
    (∑ i ∈ (mech5 n B c j).1, (mech5 n B c j).2 i) ≤ B ∧
    ∀ O : Finset (Fin n), (∑ i ∈ O, c i) ≤ B →
      v O ≤ (2 + 2 * Real.log n) * v (mech5 n B c j).1 ∧
      (2 ≤ n → v O ≤ (5 * Real.log n) * v (mech5 n B c j).1) := by sorry

end BudgetFeasibleClockAuctions.SymmetricPostedPrice
