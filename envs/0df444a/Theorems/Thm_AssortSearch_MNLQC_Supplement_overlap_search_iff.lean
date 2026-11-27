-- Prove2me | Theorems.Thm_AssortSearch_MNLQC_Supplement_overlap_search_iff
-- name    : AssortSearch.MNLQC.Supplement.overlap_search_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T06:20:54.499157+00:00
-- url     : https://prove2.me/theorems/11550ffa-c069-4a92-b41b-edb847f3f154
-- title:
--   Proof of Theorem 3 (corrected: tie searches) — the consumer searches iff $U_{\max}\le\bar U(S)$; gain exceeds $b$ iff $U_{\max}<\bar U(S)$
-- statement:
--   Let $v_1,\dots,v_n>0$ be the variants' preferences and $\mu>0$ the Gumbel scale. Let $S\subsetneq N$ be an assortment that leaves out at least one variant, and let $b>0$ be the search cost. Write
--   $$\Phi_S(y)=\int_y^\infty(\bar y-y)\,w(\bar y,S)\,d\bar y$$
--   for the expected gain from search of a consumer whose best observed utility is $y=U_{\max}$. Here $w(\cdot,S)$ is the density of the best utility $\max_{i\in\bar S}U_i$ among the variants outside the assortment. Let $\bar U(S)$ be the search threshold, the unique solution of $\Phi_S(\bar U(S))=b$ in (4). Then for every real $y$:
--
--   1. the consumer searches by rule (5), $\Phi_S(y)\ge b$, if and only if $y\le\bar U(S)$;
--   2. the gain from search strictly exceeds the cost, $\Phi_S(y)>b$, if and only if $y<\bar U(S)$.
--
--   The paper states this as "a consumer searches if and only if $U_{\max}$ is less than the threshold $\bar U(S)$". It is the step that turns the search rule into a threshold event on the best utility in the computation of the overlapping demand in Theorem 3. The paper asserts it in the proof of Theorem 3, from the fact that the left-hand side of (5) is decreasing in $y$.
--
--   **Formalization Note** $\Phi_S$ is `AssortSearch.FullAssort.searchGain` (a Lebesgue integral over $(y,\infty)$). $w(\cdot,S)$ is its closed form, whose density property is the published `outside_max_law`. $\bar U(S)$ is `AssortSearch.FullAssort.Ubar`, the least $u$ with $\Phi_S(u)\le b$; the published `theorem_3_threshold` shows it solves (4) uniquely.
--
--   Differences from the source:
--   - correction: with rule (5) "the consumer searches if ∫_y^∞ (ȳ − y) w(ȳ, S) dȳ ≥ b", "a consumer searches if and only if U_max is less than the threshold Ū(S)" → Φ_S(y) ≥ b iff y ≤ Ū(S), and Φ_S(y) > b iff y < Ū(S); reason: at y = Ū(S) equation (4) gives Φ_S(y) = b, so under rule (5) as printed the consumer searches at the threshold and the printed "less than" fails at that single point (counterexample: y = Ū(S)); the strict form Φ_S(y) > b is exactly the printed "less than". Evidence: (4) and (5) on p. 11. No case is excluded; the tie has probability zero under the continuous Gumbel law
--   - encoding: the threshold Ū(S) of the overlapping model → hypotheses S ≠ N and b > 0; reason: Ū(S) is defined as the solution of (4) only when S̄ is nonempty and b > 0; at S = N, w ≡ 0 and the consumer never searches. Only undefined cases are excluded
--   - encoding: preferences v_i = exp((u_i − p_i)/μ) → arbitrary preferences v_i > 0; reason: every positive v_i is exp((u_i − p_i)/μ) for some net utility, and the statement depends on the utilities only through the v_i
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 11 (PDF 13), proof of Theorem 3, rule (5) and "A consumer searches if and only if U_max is less than the threshold Ū(S)"

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_AssortSearch_Cannibal_Model
import Definitions.Def_AssortSearch_FullAssort_Model
import Definitions.Def_AssortSearch_HeurEq_Model
import Definitions.Def_AssortSearch_MNLQC_Supplement_Model

open MeasureTheory RetailVariety.Structure

namespace AssortSearch.MNLQC.Supplement

/-- Proof of Theorem 3 (p. 11): for an assortment `S ⊊ N` and a search cost `b > 0`, the consumer
whose best utility in the assortment is `y = U_max` searches by rule (5), `Φ_S(y) ≥ b`, exactly when
`y ≤ Ū(S)`; and the search gain strictly exceeds `b` exactly when `y < Ū(S)`. -/
theorem overlap_search_iff {n : ℕ} (μ : ℝ) (hμ : 0 < μ) (v : Fin n → ℝ) (hv : ∀ i, 0 < v i)
    (S : Finset (Fin n)) (hS : S ≠ Finset.univ) (b : ℝ) (hb : 0 < b) (y : ℝ) :
    (b ≤ AssortSearch.FullAssort.searchGain μ v S y ↔ y ≤ AssortSearch.FullAssort.Ubar μ v S b) ∧
      (b < AssortSearch.FullAssort.searchGain μ v S y ↔
        y < AssortSearch.FullAssort.Ubar μ v S b) := by sorry

end AssortSearch.MNLQC.Supplement
