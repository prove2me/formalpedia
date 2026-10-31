-- Prove2me | Theorems.Thm_FirstChoiceDesign_fact_3
-- name    : FirstChoiceDesign.fact_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:27:15.117851+00:00
-- url     : https://prove2.me/theorems/52cc6e2c-83a9-4cbc-8a03-bab57029d419
-- title:
--   Fact 3, p.41 — a switch below the cutoff preserves stable matchings
-- statement:
--   Let $\delta_s(r)$ switch $i'$ and $i''$ in $r_s$, where $\rho^\varphi_{i's}=\rho^\varphi_{i''s}$ and $\min\{\rho^\varphi_{i's}+r_{i's},\rho^\varphi_{i''s}+r_{i''s}\}>\rho^\varphi_{is}+r_{is}$ for all $i$ with $D_{is}(r)=1$. Then every $(\rho^\varphi,r)$-stable matching is also $(\rho^\varphi,(\delta_s(r),r_{-s}))$-stable.
--
--   This is one half of the comparison of stable sets behind Lemma 3.
--
--   Differences from the source:
--   - generalization: K may change with |I| (p.6); Definition 1 has one (f^φ, g^φ); Boston’s g depends on K → GDA carries K n, f n, g n for each student count n; reason: functions constant in n give one K, f, g, and a family with K depending on |I| and f, g depending on K is the composite with K(n); so the source’s mechanisms are all instances
--   - reading: f^φ, g^φ : ℕ → ℕ with ℕ the positive integers (p.6) → ℕ → ℕ with 0 in the codomain, monotone on the positive integers; reason: the source’s own DA mechanism has g^φ(n) = 0 (p.8)
--   - encoding: finite sets I, S; strict preferences ≻_i over S ∪ {∅} → Fin n, Fin m; injective u i : Option (Fin m) → ℕ, smaller is better; reason: the same instances, for all n, m
--   - encoding: r ∈ [0,1], no tie at a school (p.7) → Tieless r: numbers in the open interval (0,1), injective at each school; reason: footnote 9 says r_is is in (0,1); the boundary is null, every order reachable on [0,1] is reachable on (0,1), and without it Definition 1’s order need not be strict
--   - reading: (s, i) blocks μ if … there exists ī ∈ I with i ≻^φ_{r_s} ī (p.41) → ī ∈ μ_s; reason: plainly meant (Roth–Sotomayor): with ī ∈ I almost nothing is stable
--   - encoding: "If there are no such i′ and i″, let δ_s(r) be the same as r_s" → not stated; i′, i″ are hypotheses; reason: the omitted case is the identity
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), Fact 3, p.41

import Definitions.Def_FirstChoiceDesign_IsStable
import Definitions.Def_FirstChoiceDesign_BelowCutoff
import Definitions.Def_FirstChoiceDesign_Swap

namespace FirstChoiceDesign

open GaleShapley1962.Admissions

/-- Fact 3, Cowles Foundation DP No. 2056R, p.41. For `δ_s(r)` satisfying the conditions of Lemma 3, every
`(ρ^φ, r)`-stable matching is also `(ρ^φ, (δ_s(r), r_{-s}))`-stable.

**Formalization Note** `swapAt s i' i'' r` is `(δ_s(r), r_{-s})`. The clause "If there are no such
`i'` and `i''`, let `δ_s(r)` be the same as `r_s`" is the identity, for which the claim is trivial. -/
theorem fact_3 {n m : ℕ} (φ : GDA) (X : Problem (φ.K n) n m) (r : Lottery n m) (hr : Tieless r)
    (s : Fin m) (i' i'' : Fin n) (hδ : BelowCutoff φ X s r i' i'') (μ : Assignment n m)
    (hμ : IsStable φ X r μ) : IsStable φ X (swapAt s i' i'' r) μ := by sorry

end FirstChoiceDesign
