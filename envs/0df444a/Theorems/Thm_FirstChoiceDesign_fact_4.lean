-- Prove2me | Theorems.Thm_FirstChoiceDesign_fact_4
-- name    : FirstChoiceDesign.fact_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:26:49.057642+00:00
-- url     : https://prove2.me/theorems/a9f5708e-45da-4b76-8de5-cac606614f52
-- title:
--   Fact 4, p.42 — under strategy-proofness the converse of Fact 3 holds
-- statement:
--   Let $\varphi$ be strategy-proof for schools and let $\delta_s(r)$ be as in Fact 3. Then every $(\rho^\varphi,(\delta_s(r),r_{-s}))$-stable matching is also $(\rho^\varphi,r)$-stable.
--
--   With Fact 3 this says that the two lottery profiles have the same stable matchings.
--
--   Differences from the source:
--   - generalization: K may change with |I| (p.6); Definition 1 has one (f^φ, g^φ); Boston’s g depends on K → GDA carries K n, f n, g n for each student count n; reason: functions constant in n give one K, f, g, and a family with K depending on |I| and f, g depending on K is the composite with K(n); so the source’s mechanisms are all instances
--   - reading: f^φ, g^φ : ℕ → ℕ with ℕ the positive integers (p.6) → ℕ → ℕ with 0 in the codomain, monotone on the positive integers; reason: the source’s own DA mechanism has g^φ(n) = 0 (p.8)
--   - encoding: finite sets I, S; strict preferences ≻_i over S ∪ {∅} → Fin n, Fin m; injective u i : Option (Fin m) → ℕ, smaller is better; reason: the same instances, for all n, m
--   - encoding: r ∈ [0,1], no tie at a school (p.7) → Tieless r: numbers in the open interval (0,1), injective at each school; reason: footnote 9 says r_is is in (0,1); the boundary is null, every order reachable on [0,1] is reachable on (0,1), and without it Definition 1’s order need not be strict
--   - generalization: reports (ρ_s, r_s) ∈ Γ: ρ_is + r_is ≠ ρ_js + r_js, r ∈ [0,1] (p.13) → ValidReport: numbers in the open interval (0,1), distinct at the school; reason: a subset of Γ, so strategy-proofness in Lean is implied by the source’s and the theorem assumes less; reports in Γ with equal lottery numbers leave Definition 1’s order non-strict and φ undefined
--   - encoding: a preference ≻_s over subsets of I with its weak preference ⪰_s (p.14) → a strict total order pref, with WeakPref := pref ∨ =; reason: a preference is read as a strict total order; a hypothesis over fewer preferences is implied by one over more, and clause (2)–(3) orders are of this kind
--   - reading: (s, i) blocks μ if … there exists ī ∈ I with i ≻^φ_{r_s} ī (p.41) → ī ∈ μ_s; reason: plainly meant (Roth–Sotomayor): with ī ∈ I almost nothing is stable
--   - encoding: "If there are no such i′ and i″, let δ_s(r) be the same as r_s" → not stated; i′, i″ are hypotheses; reason: the omitted case is the identity
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), Fact 4, p.42

import Definitions.Def_FirstChoiceDesign_IsStable
import Definitions.Def_FirstChoiceDesign_BelowCutoff
import Definitions.Def_FirstChoiceDesign_Swap
import Definitions.Def_FirstChoiceDesign_StrategyProofForSchools

namespace FirstChoiceDesign

open GaleShapley1962.Admissions

/-- Fact 4, Cowles Foundation DP No. 2056R, p.42. If `φ` is strategy-proof for schools, then for `δ_s(r)` satisfying
the conditions of Lemma 3, every `(ρ^φ, (δ_s(r), r_{-s}))`-stable matching is also
`(ρ^φ, r)`-stable. -/
theorem fact_4 (φ : GDA) (hφ : StrategyProofForSchools φ) {n m : ℕ} (X : Problem (φ.K n) n m)
    (r : Lottery n m) (hr : Tieless r) (s : Fin m) (i' i'' : Fin n)
    (hδ : BelowCutoff φ X s r i' i'') (μ : Assignment n m)
    (hμ : IsStable φ X (swapAt s i' i'' r) μ) : IsStable φ X r μ := by sorry

end FirstChoiceDesign
