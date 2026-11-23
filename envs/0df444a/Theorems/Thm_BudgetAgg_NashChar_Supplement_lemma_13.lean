-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_Supplement_lemma_13
-- name    : BudgetAgg.NashChar.Supplement.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T06:10:17.192398+00:00
-- url     : https://prove2.me/theorems/e1886580-25ce-48d8-9b46-a3f53c68880f
-- title:
--   Lemma 13 (used in the proofs of Theorems 5 and 6) — m = 2: continuous strategyproof mechanisms agreeing on single-minded profiles agree everywhere
-- statement:
--   Let $m=2$ and let $U\subseteq U_{SP}$ be any domain with at least one utility per peak. If $f$ and $g$ are continuous mechanisms $[0,1]^n\to[0,1]$, both strategyproof on $U$, and $f(P)=g(P)$ for every single-minded profile $P\in\{0,1\}^n$, then
--
--   $$f(P)=g(P)\qquad\text{for every profile }P\in[0,1]^n.$$
--
--   This is the reduction behind the characterizations of Theorems 5 and 6.
--
--   **Formalization Note** $n\ge1$.
--
--   Differences from the source:
--   - encoding: m = 2: outcomes and peaks are scalars in [0, 1], the share of b (§7, p. 17) → Profile2 n = Fin n → unitInterval, Mechanism2 n = Profile2 n → unitInterval (tops-only); reason: the identification of ∆2 with [0, 1] made on p. 17
--   - encoding: arbitrary domain U ⊆ U_SP with at least one utility per peak (§7, p. 17); single-peakedness = star-shapedness (1) for m = 2 → U : Set (ℝ → ℝ) with IsSPDomain U: every u ∈ U satisfies (1) on [0, 1] at some peak p, and every p ∈ [0, 1] is the peak of some u ∈ U; values of u outside [0, 1] are never used; reason: a utility on [0, 1] extends to ℝ in any way; condition (1) is evaluated only on [0, 1]
--   - encoding: strategyproofness (Definition 8, |N′| = 1) on the domain U → IsSP2 U f: for every i, P, misreport p′ and u ∈ U single-peaked at the true peak P i, u(f(P with p_i replaced by p′)) ≤ u(f(P)); reason: an agent with peak p_i may hold any utility of U peaked at p_i, so the inequality must hold for each of them
--   - encoding: continuity in the ℓ1 distance (Definition 7) → Continuous f for the product topology on Fin n → unitInterval and the subspace topology on unitInterval; reason: for m = 2 the ℓ1 distance on ∆2 is twice the distance of the b-shares, and all norms on a finite-dimensional space induce the same topology (p. 8)
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 37, Lemma 13 (proof pp. 37–38)

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Supplement_TwoAlt

namespace BudgetAgg.NashChar.Supplement

/-- Lemma 13, p. 37: for `m = 2` and any admissible domain `U ⊆ U_SP`, two continuous
strategyproof mechanisms that agree on all single-minded profiles agree everywhere. -/
theorem lemma_13 {n : ℕ} [NeZero n] (U : Set (ℝ → ℝ)) (hU : IsSPDomain U)
    (f g : Mechanism2 n) (hf_cont : Continuous f) (hg_cont : Continuous g)
    (hf_sp : IsSP2 U f) (hg_sp : IsSP2 U g)
    (hagree : ∀ P, IsSingleMinded2 P → f P = g P) :
    ∀ P, f P = g P := by sorry

end BudgetAgg.NashChar.Supplement
