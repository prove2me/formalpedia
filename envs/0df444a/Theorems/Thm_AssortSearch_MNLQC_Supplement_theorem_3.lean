-- Prove2me | Theorems.Thm_AssortSearch_MNLQC_Supplement_theorem_3
-- name    : AssortSearch.MNLQC.Supplement.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T06:21:30.369329+00:00
-- url     : https://prove2.me/theorems/eacf20b8-d2ba-4993-81a6-b3cdc3e6813d
-- title:
--   Theorem 3 — overlapping-model demand $q_i^{so}(S)=q_i^m(S)(1-H(\bar U(S),S))$, with $\bar U(S)$ the unique solution of (4)
-- statement:
--   Consider the random-utility model with i.i.d. zero-mean Gumbel shocks $\zeta_0,\zeta_1,\dots,\zeta_n$ of scale $\mu>0$. Variant $j$ has utility $U_j=(u_j-p_j)+\zeta_j$ and preference $v_j=\exp((u_j-p_j)/\mu)$. Not purchasing has utility $U_0=u_0+\zeta_0$ and preference $v_0=\exp(u_0/\mu)$. Let $S\subsetneq N$ be an assortment that leaves out at least one variant, and let $b>0$ be the search cost of the overlapping assortment model. Let $w(\bar y,S)$ be the density of $\max_{i\in\bar S}U_i$, the maximum utility in the set $\bar S=N-S$. Then:
--
--   1. the equation
--   $$\int_{u}^{\infty}(\bar y-u)\,w(\bar y,S)\,d\bar y=b \tag{4}$$
--   has exactly one solution $u=\bar U(S)$;
--   2. for every $i\in S$, variant $i$'s demand in the overlapping assortment model is
--   $$q_i^{so}(S)=q_i^m(S)\,\big(1-H(\bar U(S),S)\big),$$
--   where $q_i^m(S)=v_i/(\sum_{j\in S}v_j+v_0)$ is the MNL share (2), $H(\bar U,S)=\exp\big(-\lambda(v_0+\sum_{j\in S}v_j)\big)$ and $\lambda=\exp[-(\bar U/\mu+\gamma)]$ as in Theorem 1, with $\gamma$ Euler's constant.
--
--   Here $q_i^{so}(S)$ is the probability that variant $i$ has the highest utility in $S$, beats not purchasing, and the consumer does not search by rule (5), $\int_{U_i}^\infty(\bar y-U_i)w(\bar y,S)\,d\bar y<b$. As in the independent model, demand is a fraction of the MNL demand. Unlike there, the search threshold depends on the assortment.
--
--   **Formalization Note** The demand is `overlapProb`, a probability under the product Gumbel law, not the closed form `AssortSearch.FullAssort.demandSO`; the theorem shows that the two agree. $w(\cdot,S)$ is the closed form `AssortSearch.FullAssort.w`, whose density property is the published `outside_max_law`. Clause 1 restates the published `theorem_3_threshold` for these preferences. Variants are `Fin n`, 0-based, and the no-purchase option is the index `none`.
--
--   Differences from the source:
--   - encoding: S an assortment, b the single search cost, Ū(S) "the unique solution" of (4) → hypotheses S ≠ N and b > 0; reason: (4) has a solution only when S̄ is nonempty and b > 0 (at S = N, w ≡ 0 and the left side vanishes); this is the domain on which the theorem's Ū(S) exists. At S = N the paper's model has no search (p. 28)
--   - encoding: "variant i's demand" q_i^so(S) → the probability, under the product of the Gumbel law over the no-purchase option and the n variants, of the event that i is the best in S, beats U_0 and Φ_S(U_i) < b; reason: demand per consumer with the population normalised to 1, as in Theorem 1; rule (5) searches on ties, as printed
--   - encoding: w(ȳ, S), the density of max_{i∈S̄} U_i → the closed form (V̄_S/μ) e^{−(ȳ/μ+γ)} exp(−e^{−(ȳ/μ+γ)} V̄_S) of AssortSearch.FullAssort.w; reason: the published outside_max_law proves this is the density of the maximum; the paper calls it "straightforward to evaluate"
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 11 (PDF 13), Theorem 3 and (4); proof: p. 11, rule (5), referring to the proof of Theorem 1 (p. 8)

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_AssortSearch_Cannibal_Model
import Definitions.Def_AssortSearch_FullAssort_Model
import Definitions.Def_AssortSearch_HeurEq_Model
import Definitions.Def_AssortSearch_MNLQC_Supplement_Model

open MeasureTheory RetailVariety.Structure

namespace AssortSearch.MNLQC.Supplement

/-- **Theorem 3** (p. 11), overlapping assortment model. Let the shocks be i.i.d. zero-mean Gumbel
of scale `μ > 0`, let `v_j = exp(a_j/μ)`, `v_0 = exp(u_0/μ)`, `S ⊊ N` and `b > 0`. Then (4),
`∫_u^∞ (ȳ − u) w(ȳ, S) dȳ = b`, has exactly one solution `u = Ū(S)`, and for every `i ∈ S` the
probability that the consumer buys `i` is `q_i^so(S) = q_i^m(S) (1 − H(Ū(S), S))`. -/
theorem theorem_3 {n : ℕ} (μ : ℝ) (hμ : 0 < μ) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : AssortSearch.Cannibal.IsZeroMeanGumbel μ G) (a : Fin n → ℝ) (u0 b : ℝ) (hb : 0 < b)
    (S : Finset (Fin n)) (hS : S ≠ Finset.univ) :
    (AssortSearch.FullAssort.searchGain μ (AssortSearch.Cannibal.pref μ a) S
          (AssortSearch.FullAssort.Ubar μ (AssortSearch.Cannibal.pref μ a) S b) = b ∧
        ∀ u : ℝ, AssortSearch.FullAssort.searchGain μ (AssortSearch.Cannibal.pref μ a) S u = b →
          u = AssortSearch.FullAssort.Ubar μ (AssortSearch.Cannibal.pref μ a) S b) ∧
      ∀ i ∈ S, overlapProb G μ a u0 b S i =
        share (AssortSearch.Cannibal.pref μ a) (AssortSearch.Cannibal.pref0 μ u0) S i *
          (1 - AssortSearch.Cannibal.H μ
            (AssortSearch.FullAssort.Ubar μ (AssortSearch.Cannibal.pref μ a) S b)
            (AssortSearch.Cannibal.pref μ a) (AssortSearch.Cannibal.pref0 μ u0) S) := by sorry

end AssortSearch.MNLQC.Supplement
