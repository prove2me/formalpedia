-- Prove2me | Theorems.Thm_FirstChoiceDesign_fact_1
-- name    : FirstChoiceDesign.fact_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:26:33.336878+00:00
-- url     : https://prove2.me/theorems/2cff530f-2ced-4192-955d-844a66d3b158
-- title:
--   Fact 1, p.41 — every stable matching gives a school a set weakly better than $\varphi$ does
-- statement:
--   Let $X$ be an assignment problem, $r$ a lottery number profile and $\varphi$ a gDA mechanism. For any $(\rho^\varphi,r)$-stable matching $\mu$, any school $s$ and any preference $\succ^\varphi_s$ responsive with respect to $(c_s,\rho^\varphi,r)$,
--
--   $$
--   \mu_s\succeq^\varphi_s\varphi_s(\rho,r).
--   $$
--
--   So the student-proposing outcome is the worst stable outcome for every school. This is what makes the mechanism's outcome identifiable among stable matchings in the proof of Lemma 3.
--
--   **Formalization Note** The responsive criterion is the modified one, $\rho^\varphi_{is}+r_{is}$.
--
--   Differences from the source:
--   - generalization: K may change with |I| (p.6); Definition 1 has one (f^φ, g^φ); Boston’s g depends on K → GDA carries K n, f n, g n for each student count n; reason: functions constant in n give one K, f, g, and a family with K depending on |I| and f, g depending on K is the composite with K(n); so the source’s mechanisms are all instances
--   - reading: f^φ, g^φ : ℕ → ℕ with ℕ the positive integers (p.6) → ℕ → ℕ with 0 in the codomain, monotone on the positive integers; reason: the source’s own DA mechanism has g^φ(n) = 0 (p.8)
--   - encoding: finite sets I, S; strict preferences ≻_i over S ∪ {∅} → Fin n, Fin m; injective u i : Option (Fin m) → ℕ, smaller is better; reason: the same instances, for all n, m
--   - encoding: r ∈ [0,1], no tie at a school (p.7) → Tieless r: numbers in the open interval (0,1), injective at each school; reason: footnote 9 says r_is is in (0,1); the boundary is null, every order reachable on [0,1] is reachable on (0,1), and without it Definition 1’s order need not be strict
--   - reading: (s, i) blocks μ if … there exists ī ∈ I with i ≻^φ_{r_s} ī (p.41) → ī ∈ μ_s; reason: plainly meant (Roth–Sotomayor): with ī ∈ I almost nothing is stable
--   - encoding: a preference ≻_s over subsets of I with its weak preference ⪰_s (p.14) → a strict total order pref, with WeakPref := pref ∨ =; reason: a preference is read as a strict total order; a hypothesis over fewer preferences is implied by one over more, and clause (2)–(3) orders are of this kind
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), Fact 1, p.41 (Roth and Sotomayor (1992), Theorem 5.8)

import Definitions.Def_FirstChoiceDesign_IsStable
import Definitions.Def_FirstChoiceDesign_Responsive

namespace FirstChoiceDesign

open GaleShapley1962.Admissions

/-- Fact 1 (Roth and Sotomayor (1992)'s Theorem 5.8), Cowles Foundation DP No. 2056R, p.41. For any
`(ρ^φ, r)`-stable matching `μ`, any school `s` and any preference responsive with respect to
`(c_s, ρ^φ, r)`, it holds `μ_s ⪰^φ_s φ_s(ρ, r)`.

**Formalization Note** The responsiveness criterion is the modified one, `ρ^φ_is + r_is`. -/
theorem fact_1 {n m : ℕ} (φ : GDA) (X : Problem (φ.K n) n m) (r : Lottery n m) (hr : Tieless r)
    (μ : Assignment n m) (hμ : IsStable φ X r μ) (s : Fin m)
    (pref : Finset (Fin n) → Finset (Fin n) → Prop) (hpref : IsStrictTotalOrder _ pref)
    (hresp : Responsive (X.c s) (fun i => φ.score X.toSetting X.ρ r i s) pref) :
    WeakPref pref (seats μ s) (assigned φ X.toSetting X.ρ r s) := by sorry

end FirstChoiceDesign
