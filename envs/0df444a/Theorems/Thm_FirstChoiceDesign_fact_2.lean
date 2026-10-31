-- Prove2me | Theorems.Thm_FirstChoiceDesign_fact_2
-- name    : FirstChoiceDesign.fact_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:26:59.41312+00:00
-- url     : https://prove2.me/theorems/f1b1d4e3-8b39-45f9-9d4f-9d94a4bae0e1
-- title:
--   Fact 2, p.41 — a school prefers every student of its better stable set
-- statement:
--   Let $\mu,\mu'$ be $(\rho^\varphi,r)$-stable matchings with $\mu_s\succ^\varphi_s\mu'_s$ for some preference $\succ^\varphi_s$ responsive with respect to $(c_s,\rho^\varphi_s,r_s)$. Then for any $i\in\mu_s$ and $i'\in\mu'_s\setminus\mu_s$,
--
--   $$
--   i\succ^\varphi_{r_s}i',\quad\text{i.e.,}\quad\rho^\varphi_{is}+r_{is}<\rho^\varphi_{i's}+r_{i's}.
--   $$
--
--   Together with Fact 1 it locates the students outside the outcome's set relative to the cutoff.
--
--   Differences from the source:
--   - generalization: K may change with |I| (p.6); Definition 1 has one (f^φ, g^φ); Boston’s g depends on K → GDA carries K n, f n, g n for each student count n; reason: functions constant in n give one K, f, g, and a family with K depending on |I| and f, g depending on K is the composite with K(n); so the source’s mechanisms are all instances
--   - reading: f^φ, g^φ : ℕ → ℕ with ℕ the positive integers (p.6) → ℕ → ℕ with 0 in the codomain, monotone on the positive integers; reason: the source’s own DA mechanism has g^φ(n) = 0 (p.8)
--   - encoding: finite sets I, S; strict preferences ≻_i over S ∪ {∅} → Fin n, Fin m; injective u i : Option (Fin m) → ℕ, smaller is better; reason: the same instances, for all n, m
--   - encoding: r ∈ [0,1], no tie at a school (p.7) → Tieless r: numbers in the open interval (0,1), injective at each school; reason: footnote 9 says r_is is in (0,1); the boundary is null, every order reachable on [0,1] is reachable on (0,1), and without it Definition 1’s order need not be strict
--   - reading: (s, i) blocks μ if … there exists ī ∈ I with i ≻^φ_{r_s} ī (p.41) → ī ∈ μ_s; reason: plainly meant (Roth–Sotomayor): with ī ∈ I almost nothing is stable
--   - encoding: a preference ≻_s over subsets of I with its weak preference ⪰_s (p.14) → a strict total order pref, with WeakPref := pref ∨ =; reason: a preference is read as a strict total order; a hypothesis over fewer preferences is implied by one over more, and clause (2)–(3) orders are of this kind
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), Fact 2, p.41 (Roth and Sotomayor (1989), Theorem 4)

import Definitions.Def_FirstChoiceDesign_IsStable
import Definitions.Def_FirstChoiceDesign_Responsive

namespace FirstChoiceDesign

open GaleShapley1962.Admissions

/-- Fact 2 (Roth and Sotomayor (1989)'s Theorem 4), Cowles Foundation DP No. 2056R, p.41. If `μ, μ'` are
`(ρ^φ, r)`-stable with `μ_s ≻^φ_s μ'_s` for some preference responsive with respect to
`(c_s, ρ^φ_s, r_s)`, then for any `i ∈ μ_s` and `i' ∈ μ'_s ∖ μ_s`,
`ρ^φ_is + r_is < ρ^φ_i's + r_i's`. -/
theorem fact_2 {n m : ℕ} (φ : GDA) (X : Problem (φ.K n) n m) (r : Lottery n m) (hr : Tieless r)
    (μ μ' : Assignment n m) (hμ : IsStable φ X r μ) (hμ' : IsStable φ X r μ') (s : Fin m)
    (pref : Finset (Fin n) → Finset (Fin n) → Prop) (hpref : IsStrictTotalOrder _ pref)
    (hresp : Responsive (X.c s) (fun i => φ.score X.toSetting X.ρ r i s) pref)
    (hpr : pref (seats μ s) (seats μ' s)) (i i' : Fin n) (hi : i ∈ seats μ s)
    (hi' : i' ∈ seats μ' s \ seats μ s) :
    φ.score X.toSetting X.ρ r i s < φ.score X.toSetting X.ρ r i' s := by sorry

end FirstChoiceDesign
