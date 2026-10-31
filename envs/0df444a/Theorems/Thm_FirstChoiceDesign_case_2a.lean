-- Prove2me | Theorems.Thm_FirstChoiceDesign_case_2a
-- name    : FirstChoiceDesign.case_2a
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:26:20.8478+00:00
-- url     : https://prove2.me/theorems/4af49161-01ad-4fa4-b24c-5e021d7570ab
-- title:
--   Case 2.a, p.55 — a switch of two assigned students keeps first-choice assignments
-- statement:
--   Let $r$ be consistent with the regime and let $i',i''$ be consecutive in $r_s$ within $\mathit{First}_s(r)$ with $D_{i's}(r)=D_{i''s}(r)=1$. Then there exists $j$ with $D_{js}(r)=1$ such that
--
--   $$
--   \max\{\rho^\varphi_{i's}+r_{i's},\rho^\varphi_{i''s}+r_{i''s}\}\le\rho^\varphi_{js}+r_{js},
--   $$
--
--   and $D_{is}(\hat\sigma(r))=D_{is}(r)$ for all $i\in\mathit{First}_s(r)$, under MTB and under STB. So Case 2.a of the main proof cannot occur.
--
--   No strategy-proofness is assumed.
--
--   Differences from the source:
--   - generalization: K may change with |I| (p.6); Definition 1 has one (f^φ, g^φ); Boston’s g depends on K → GDA carries K n, f n, g n for each student count n; reason: functions constant in n give one K, f, g, and a family with K depending on |I| and f, g depending on K is the composite with K(n); so the source’s mechanisms are all instances
--   - reading: f^φ, g^φ : ℕ → ℕ with ℕ the positive integers (p.6) → ℕ → ℕ with 0 in the codomain, monotone on the positive integers; reason: the source’s own DA mechanism has g^φ(n) = 0 (p.8)
--   - encoding: finite sets I, S; strict preferences ≻_i over S ∪ {∅} → Fin n, Fin m; injective u i : Option (Fin m) → ℕ, smaller is better; reason: the same instances, for all n, m
--   - encoding: r ∈ [0,1], no tie at a school (p.7) → Tieless r: numbers in the open interval (0,1), injective at each school; reason: footnote 9 says r_is is in (0,1); the boundary is null, every order reachable on [0,1] is reachable on (0,1), and without it Definition 1’s order need not be strict
--   - reading: "there exists j with D_is(r) = 1" (p.55) → D_js(r) = 1; reason: the index i is a slip; the rest of the sentence is about j
--   - encoding: derivation of a contradiction to D_is(σ̂(r)) ≠ D_is(r) → the positive statement D_is(σ̂(r)) ↔ D_is(r) for all i ∈ First_s(r); reason: the same claim; it follows the printed conclusion "This implies D_is(σ̂(r)) = D_is(r) for all i ∈ First_s(r)"
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), Appendix A.1, Case 2.a, p.55, "Then there exists j with"

import Definitions.Def_FirstChoiceDesign_IsPivot
import Definitions.Def_FirstChoiceDesign_Swap

namespace FirstChoiceDesign

/-- Case 2.a, Cowles Foundation DP No. 2056R, p.55. If `i', i''` are consecutive in `r_s` within `First_s(r)` and
`D_{i' s}(r) = D_{i'' s}(r) = 1`, then there exists `j` with `D_js(r) = 1` such that
`max{ρ^φ_i's + r_i's, ρ^φ_i''s + r_i''s} ≤ ρ^φ_js + r_js`, and `D_is(σ̂(r)) = D_is(r)` for all
`i ∈ First_s(r)`, under MTB and STB alike. So the case "cannot occur" in the proof.

**Formalization Note** The page's first sentence has `D_is(r)` where `D_js(r)` is meant. Such a pair is
never the pivot pair, because a pivot pair has different `D`. `r` is consistent with the regime. -/
theorem case_2a {n m : ℕ} (φ : GDA) (X : Problem (φ.K n) n m) (r : Lottery n m)
    (hr : Potential φ.regime r) (s : Fin m) (i' i'' : Fin n) (hc : Consecutive φ X s r i' i'')
    (h' : D φ X i' s r) (h'' : D φ X i'' s r) :
    (∃ j, D φ X j s r ∧
      max (φ.score X.toSetting X.ρ r i' s) (φ.score X.toSetting X.ρ r i'' s) ≤
        φ.score X.toSetting X.ρ r j s) ∧
      ∀ i ∈ First φ X s r, (D φ X i s (swapReg φ.regime s i' i'' r) ↔ D φ X i s r) := by sorry

end FirstChoiceDesign
