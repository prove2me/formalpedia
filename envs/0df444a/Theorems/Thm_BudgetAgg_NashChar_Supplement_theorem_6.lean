-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_Supplement_theorem_6
-- name    : BudgetAgg.NashChar.Supplement.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:13:11.425011+00:00
-- url     : https://prove2.me/theorems/9d146fc3-18fd-4b24-bc82-5d815e8331e7
-- title:
--   Theorem 6 — m = 2, any domain U ⊆ U_SP: the uniform phantom rule is the only continuous strategyproof proportional mechanism
-- statement:
--   Let $m=2$ and let $U\subseteq U_{SP}$ be any domain with at least one utility per peak. A mechanism $f:[0,1]^n\to[0,1]$ is continuous, strategyproof on $U$ and proportional if and only if it is the **uniform phantom rule**:
--
--   $$f(P)=\mathrm{med}\Big(p_1,\dots,p_n,0,\tfrac1n,\tfrac2n,\dots,1\Big)\qquad\text{for every profile }P.$$
--
--   This is a companion theorem: the goal (Theorem 3) is not proved from it. Its proof rests on Lemma 13.
--
--   **Formalization Note** $n\ge1$. Proportionality is stated for the share of $b$; the share of $a$ is its complement.
--
--   Differences from the source:
--   - encoding: m = 2: outcomes and peaks are scalars in [0, 1], the share of b (§7, p. 17) → Profile2 n = Fin n → unitInterval, Mechanism2 n = Profile2 n → unitInterval (tops-only); reason: the identification of ∆2 with [0, 1] made on p. 17
--   - encoding: arbitrary domain U ⊆ U_SP with at least one utility per peak (§7, p. 17); single-peakedness = star-shapedness (1) for m = 2 → U : Set (ℝ → ℝ) with IsSPDomain U: every u ∈ U satisfies (1) on [0, 1] at some peak p, and every p ∈ [0, 1] is the peak of some u ∈ U; values of u outside [0, 1] are never used; reason: a utility on [0, 1] extends to ℝ in any way; condition (1) is evaluated only on [0, 1]
--   - encoding: strategyproofness (Definition 8, |N′| = 1) on the domain U → IsSP2 U f: for every i, P, misreport p′ and u ∈ U single-peaked at the true peak P i, u(f(P with p_i replaced by p′)) ≤ u(f(P)); reason: an agent with peak p_i may hold any utility of U peaked at p_i, so the inequality must hold for each of them
--   - encoding: med(x_1, …, x_{2k+1}) (p. 18) → med sorts the 2k+1 values ascending and takes index k (0-based), i.e. the (k+1)-th smallest; reason: definition of the median of an odd number of reals
--   - reading: "the only continuous mechanism that satisfies strategyproofness and proportionality is the uniform phantom rule" → an iff: f is continuous, strategyproof on U and proportional exactly when f is the uniform phantom rule; reason: "the only … is" asserts that the uniform phantom rule has the properties and that no other mechanism does; the proof on p. 39 uses both
--   - encoding: proportionality f(P)_j = Σ_i p_{i,j}/n for j ∈ {a, b} → f(P) = Σ_i p_i / n for the share of b; reason: the share of a is 1 minus the share of b on both sides
--   - encoding: continuity in the ℓ1 distance (Definition 7) → Continuous f for the product topology on Fin n → unitInterval and the subspace topology on unitInterval; reason: for m = 2 the ℓ1 distance on ∆2 is twice the distance of the b-shares, and all norms on a finite-dimensional space induce the same topology (p. 8)
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 18, Theorem 6 (proof p. 39)

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Supplement_TwoAlt

namespace BudgetAgg.NashChar.Supplement

/-- Theorem 6, p. 18: for `m = 2` and any admissible domain `U ⊆ U_SP`, the uniform
phantom rule is the only continuous, strategyproof and proportional mechanism. -/
theorem theorem_6 {n : ℕ} [NeZero n] (U : Set (ℝ → ℝ)) (hU : IsSPDomain U)
    (f : Mechanism2 n) :
    (Continuous f ∧ IsSP2 U f ∧ IsProportional2 f) ↔
      ∀ P, (f P : ℝ) = uniformPhantom P := by sorry

end BudgetAgg.NashChar.Supplement
