-- Prove2me | Theorems.Thm_AssortSearch_MNLQC_Supplement_theorem_8
-- name    : AssortSearch.MNLQC.Supplement.theorem_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T06:24:35.229906+00:00
-- url     : https://prove2.me/theorems/1e683c8a-4445-497d-9a0a-3a5650bb660e
-- title:
--   Theorem 8 (both search models) — the heuristic equilibrium of no-search assortment planning is never deeper than optimal, $x^*\le x^o$
-- statement:
--   A retailer can carry the $x$ most popular of $n$ product variants, with preferences $v_1\ge\dots\ge v_n>0$ and no-purchase preference $v_0>0$. Margins are monotone, $m_j\ge m_k$ whenever $v_j\ge v_k$, and the operational cost $c$ is concave and increasing on $[0,1]$ with $c(0)\ge0$. Consumers follow either the independent assortment search model (constant $\lambda>0$) or the overlapping assortment search model (Gumbel scale $\mu>0$, search cost $b>0$). The retailer plans with the traditional no-search MNL model and re-estimates the preferences from the sales of each assortment it carries.
--
--   In each model, let $x^*$ be a heuristic equilibrium of this process: $1\le x^*\le n$ and $x^*$ maximises the predicted profit $\pi(\cdot\mid\hat v(x^*))$ over the depths $0,\dots,n$. Let $x^o$ be an optimal assortment of the same model, $\pi(x^o)=\max_{0\le x\le n}\pi(x)$, such that every deeper assortment is strictly worse: $\pi(x)<\pi(x^o)$ for $x^o<x\le n$. Then
--   $$x^*\le x^o.$$
--
--   A retailer that ignores consumer search risks an assortment that is too narrow, never one that is too deep.
--
--   **Formalization Note** The statement is the conjunction of the two models. The independent conjunct is verbatim the published `AssortSearch.HeurEq.theorem_8`, with the equilibrium and optimum quantified inside. The overlapping conjunct uses `IsHeuristicEquilibriumOv`, `IsOptimalDepthOv` and `trueProfitOv` of `AssortSearch.MNLQC.Supplement.Model`, with the same hypotheses. Optimality is over depths, as in the paper's proof.
--
--   Differences from the source:
--   - reading: Theorem 8, stated once, with a proof for the independent model that ends "The similar process can be applied to show the result for the overlapping assortment model" → the conjunction of the independent-model claim (the published HeurEq.theorem_8 verbatim) and the overlapping-model claim; reason: the theorem is asserted for both search models
--   - reading: "the optimal assortment" x^o → any optimal depth x^o such that every deeper depth x^o < x ≤ n is strictly worse; reason: the definite article presumes a unique optimum, which implies the strict-deeper condition; with ties a shallower optimum can lie below the equilibrium. Excluded are instances with an equally good deeper optimum
--   - reading: an operational cost c(·), concave and increasing, with c(0) not specified → c concave and monotone on [0, 1] with c(0) ≥ 0; reason: a cost at zero demand is nonnegative in the paper's setting (its numerical costs c(q) = νq^β have c(0) = 0), and the proof's step that a nonnegative estimated variant profit implies over-estimation needs m q − c(q) ≤ 0 at q = 0. Excluded are costs with c(0) < 0; this is the hypothesis of the moderated published independent version
--   - encoding: a heuristic equilibrium x* → 1 ≤ x* ≤ n; reason: at x* = 0 nothing is observed and v̂(0) is undefined
--   - encoding: λ = exp[−(Ū/μ + γ)] of the independent model → a free parameter λ > 0; reason: every real Ū gives some λ > 0 and conversely; same instances
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 23 (PDF 25), Theorem 8; proof pp. 23–24 (PDF 25–26)

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_AssortSearch_Cannibal_Model
import Definitions.Def_AssortSearch_FullAssort_Model
import Definitions.Def_AssortSearch_HeurEq_Model
import Definitions.Def_AssortSearch_MNLQC_Supplement_Model

open MeasureTheory RetailVariety.Structure

namespace AssortSearch.MNLQC.Supplement

/-- **Theorem 8** (p. 23), in both search models: the heuristic equilibrium resulting from the
iterative application of the no-search assortment planning model never contains more variants than
the optimal assortment, `x* ≤ x^o`. In each model `x^o` maximises the true profit over the depths
`0, …, n` and every deeper depth is strictly worse; the first conjunct is the independent
assortment model, the second the overlapping assortment model. -/
theorem theorem_8 {n : ℕ} (lam μ b : ℝ) (m : Fin n → ℝ) (c : ℝ → ℝ)
    (v : Fin n → ℝ) (v0 : ℝ)
    (hv : ∀ i, 0 < v i) (hanti : Antitone v) (hv0 : 0 < v0) (hlam : 0 < lam)
    (hμ : 0 < μ) (hb : 0 < b)
    (hm : ∀ j k : Fin n, v k ≤ v j → m k ≤ m j)
    (hcc : ConcaveOn ℝ (Set.Icc 0 1) c) (hcm : MonotoneOn c (Set.Icc 0 1))
    (hc0 : 0 ≤ c 0) :
    (∀ xstar xo : ℕ, AssortSearch.HeurEq.IsHeuristicEquilibrium lam m c v v0 xstar →
      AssortSearch.HeurEq.IsOptimalDepth lam m c v v0 xo →
      (∀ x : ℕ, xo < x → x ≤ n →
        AssortSearch.HeurEq.trueProfit lam m c v v0 x <
          AssortSearch.HeurEq.trueProfit lam m c v v0 xo) →
      xstar ≤ xo) ∧
    (∀ xstar xo : ℕ, IsHeuristicEquilibriumOv μ b m c v v0 xstar →
      IsOptimalDepthOv μ b m c v v0 xo →
      (∀ x : ℕ, xo < x → x ≤ n → trueProfitOv μ b m c v v0 x < trueProfitOv μ b m c v v0 xo) →
      xstar ≤ xo) := by sorry

end AssortSearch.MNLQC.Supplement
