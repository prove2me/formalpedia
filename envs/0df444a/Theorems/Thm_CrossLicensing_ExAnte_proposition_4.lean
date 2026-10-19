-- Prove2me | Theorems.Thm_CrossLicensing_ExAnte_proposition_4
-- name    : CrossLicensing.ExAnte.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T14:39:37.384303+00:00
-- url     : https://prove2.me/theorems/607988be-7ace-4581-91cc-360806ff5cf3
-- title:
--   Proposition 4, p. 14 — the supplier's ex ante preference in three cost regions
-- statement:
--   Fix $k_1>49/144$ and licensing effectiveness $\beta\in[0,1]$. Let $P(k_2,\gamma)$ be the supplier's optimal wholesale revenue at the paper's named equilibrium innovation levels when licensing effectiveness is $\gamma$. For every admissible superior-firm cost $49/144<k_2<k_1$, the supplier's comparison of $P(k_2,\beta)$ with $P(k_2,0)$ has three regimes:
--
--   1. If $k_2<\hat k_2(k_1\mid\beta)$, then $k_2<\hat k_2(k_1\mid0)$ and $P(k_2,0)\le P(k_2,\beta)$. The threshold $\hat k_2(k_1\mid\gamma)$ strictly decreases in $\gamma\in[0,1]$, and for some $\bar\gamma<1$ no admissible $k_2$ is in this boundary region when $\gamma\in[\bar\gamma,1]$.
--   2. In $\hat k_2(k_1\mid\beta)\le k_2<\hat k_2(k_1\mid0)$, there is a single cost threshold $\tilde k_2$, depending on $k_1,\beta$ but not on $k_2$, for which $P(k_2,0)\le P(k_2,\beta)$ if and only if $k_2\le\tilde k_2$.
--   3. In $k_2\ge\hat k_2(k_1\mid0)$, there is a single cost threshold $\underline k_2$, likewise independent of $k_2$, for which $P(k_2,0)\le P(k_2,\beta)$ if and only if $\underline k_2\le k_2$. If $\beta\ge2/5$, then $P(k_2,\beta)\le P(k_2,0)$ throughout this region.
--
--   The three regions distinguish whether the innovation outcome is boundary or interior with and without licensing. Together they characterize the supplier's ex ante contract preference.
--
--   **Formalization Note** The appendix's formulas for $\tilde k_2$ and $\underline k_2$ are handled as existential single-crossing thresholds because the printed $\underline k_2$ expression is garbled. The weak inequality follows the proof's comparisons. The final $2/5$ clause corrects the appendix's apparent $\pi_s^B(\beta)$ typo to $\pi_s^I(\beta)$. The threshold binders precede the quantified cost, excluding vacuous one-sided thresholds. $P$ comes from the wholesale-price supremum, not from a closed-form definition.
-- source:
--   Wang, Huang, Lee, Cross-licensing in a Supply Chain with Asymmetric Manufacturers, SSRN 3053682 (version of 2023-04-27), p. 14 (PDF 14), Proposition 4; proof pp. A.2–A.3 (PDF 34–35)

import Definitions.Def_CrossLicensing_ExAnte_Model

namespace CrossLicensing.ExAnte

/-- Proposition 4, p. 14. The thresholds in (ii) and (iii) are chosen once
for fixed k₁ and β, before quantifying over the varying cost k₂. -/
theorem proposition_4 (k1 β : ℝ)
    (hk1 : (49 : ℝ) / 144 < k1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    (∀ k2 : ℝ, CrossLicensing.Innovation.Standing β k1 k2 → k2 < khat2 k1 β →
      k2 < khat2 k1 0 ∧
      equilibriumProfit k1 k2 0 ≤ equilibriumProfit k1 k2 β) ∧
    StrictAntiOn (fun β' : ℝ => khat2 k1 β') (Set.Icc 0 1) ∧
    khat2 k1 1 = 0 ∧
    (∃ βbar : ℝ, 0 ≤ βbar ∧ βbar < 1 ∧
      ∀ β' : ℝ, βbar ≤ β' → β' ≤ 1 →
        ∀ k2 : ℝ, CrossLicensing.Innovation.Standing β' k1 k2 → ¬ k2 < khat2 k1 β') ∧
    (∃ ktilde : ℝ, ∀ k2 : ℝ, CrossLicensing.Innovation.Standing β k1 k2 →
      khat2 k1 β ≤ k2 → k2 < khat2 k1 0 →
        (equilibriumProfit k1 k2 0 ≤ equilibriumProfit k1 k2 β ↔ k2 ≤ ktilde)) ∧
    (∃ kunder : ℝ, ∀ k2 : ℝ, CrossLicensing.Innovation.Standing β k1 k2 →
      khat2 k1 0 ≤ k2 →
        (equilibriumProfit k1 k2 0 ≤ equilibriumProfit k1 k2 β ↔ kunder ≤ k2)) ∧
    ((2 : ℝ) / 5 ≤ β → ∀ k2 : ℝ, CrossLicensing.Innovation.Standing β k1 k2 →
      khat2 k1 0 ≤ k2 →
        equilibriumProfit k1 k2 β ≤ equilibriumProfit k1 k2 0) := by sorry

end CrossLicensing.ExAnte
