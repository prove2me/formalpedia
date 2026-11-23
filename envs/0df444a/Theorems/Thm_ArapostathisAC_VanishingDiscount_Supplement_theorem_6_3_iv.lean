-- Prove2me | Theorems.Thm_ArapostathisAC_VanishingDiscount_Supplement_theorem_6_3_iv
-- name    : ArapostathisAC.VanishingDiscount.Supplement.theorem_6_3_iv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:14:46.56094+00:00
-- url     : https://prove2.me/theorems/92d9ee2b-7318-49a7-a1f4-fd593e260f91
-- title:
--   Theorem 6.3 (iv) — for a canonical triplet with bounded cost, $h^-(x)+\rho(x)/(1-\beta)\le J^*_\beta(x)\le h^+(x)+\rho(x)/(1-\beta)$
-- statement:
--   Let $(\rho,h,\pi^*)$ be a canonical triplet, i.e. $\rho,h$ bounded measurable and $J_N(x,\pi^*,h)=J^*_N(x,h)=h(x)+N\rho(x)$ for all $N\in\mathbb N_0$ and $x$ (6.4), and let the cost be bounded on $K$. Then for every $\beta\in(0,1)$ and every $x\in S$,
--   $$h^-(x)+\frac{\rho(x)}{1-\beta}\le J^*_\beta(x)\le h^+(x)+\frac{\rho(x)}{1-\beta},$$
--   where $h^+=h-\inf h$ and $h^-=h-\sup h$.
--
--   The bounds hold with the state-dependent gain $\rho(x)$; letting $\beta\uparrow1$ they give $(1-\beta)J^*_\beta(x)\to\rho(x)$. Clauses (i)–(iii), (v) and (vi) of Theorem 6.3 are published items of the base series.
--
--   **Formalization Note** $J^*_\beta\in[0,\infty]$ is the infimum over all admissible policies, and the inequalities are stated in $\mathrm{EReal}$. As for the published clauses of Theorem 6.3, the continuity Assumptions 2.2–2.3 are not hypotheses: the bounds follow from (6.4) alone.
--
--   Differences from the source:
--   - generalization: the standing Assumptions 2.2–2.3 of p. 288 → not assumed (only the canonical triplet, c ≥ 0 and c ∈ 𝓜_b(K)); reason: with J_β = (1 − β) ∑_{N≥1} β^{N−1} J_N and J_N(x, π) ≥ J*_N(x, h) − sup h = h⁻(x) + Nρ(x) (resp. J_N(x, π*) ≤ h⁺(x) + Nρ(x)) the bounds follow from (6.4) alone; p. 318 uses continuity (Assumption 6.1) only for the existence of selectors, and the published clauses (i)–(iii), (v), (vi) of Theorem 6.3 are stated without 2.2–2.3; with them added the statement is the printed one
--   - reading: (iv) for the discount factor β → every β ∈ (0, 1); reason: β ranges over (0, 1) throughout the paper
--   - encoding: J*_β(x) as real or extended-real numbers → values in [0, ∞] (lintegrals of the nonnegative cost), compared in EReal where signed terms occur; reason: Lean convention; costs are nonnegative on K (Assumption 2.1), so the instances are the same and infinite values are represented exactly
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 318, Theorem 6.3 (iv); p. 283, h⁺ and h⁻; p. 316, (6.4)

import Mathlib
import Definitions.Def_ArapostathisAC_CanonicalTriplet_CMP
import Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_BorelCriteria

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open ArapostathisAC.CanonicalTriplet

namespace ArapostathisAC.VanishingDiscount.Supplement

/-- Theorem 6.3 (iv) (p. 318). Let `(ρ, h, π*)` be a canonical triplet and `c ∈ 𝓜_b(K)`. Then for
every `β ∈ (0, 1)` and every `x ∈ S`,
`h⁻(x) + ρ(x)/(1 − β) ≤ J*_β(x) ≤ h⁺(x) + ρ(x)/(1 − β)`,
where `h⁺ = h − inf h` and `h⁻ = h − sup h` (p. 283). -/
theorem theorem_6_3_iv {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S]
    [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : BorelCMP S A) (hc : CostBounded M) (ρ h : S → ℝ) (πs : Policy M)
    (hcan : IsCanonical M ρ h πs) (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1) (x : S) :
    (((h x - ⨆ y, h y) + ρ x / (1 - β) : ℝ) : EReal) ≤ (discValue M β x : EReal) ∧
      (discValue M β x : EReal) ≤ (((h x - ⨅ y, h y) + ρ x / (1 - β) : ℝ) : EReal) := by sorry

end ArapostathisAC.VanishingDiscount.Supplement
