-- Prove2me | Theorems.Thm_FirstChoiceDesign_case_2b_closure
-- name    : FirstChoiceDesign.case_2b_closure
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:26:55.802445+00:00
-- url     : https://prove2.me/theorems/76f51918-e985-4298-bdc4-8da6f4d31504
-- title:
--   Case 2.b closure, p.57 — a breakdown at a rejected consecutive pair refutes strategy-proofness
-- statement:
--   Let $r$ be consistent with the regime, and let $i',i''$ be consecutive in $r_s$ within $\mathit{First}_s(r)$ with $D_{i's}(r)=D_{i''s}(r)=0$. If $D_{is}(\hat\sigma(r))\ne D_{is}(r)$ for some $i\in\mathit{First}_s(r)$, where $\hat\sigma$ switches $i'$ and $i''$, then $\varphi$ is not strategy-proof for schools.
--
--   This closes the main proof: Lemma 5 gives Case 1 or Case 2, Case 1 contradicts strategy-proofness by Lemma 8, Case 2.a cannot occur, and this item handles Case 2.b.
--
--   **Formalization Note** Under strategy-proofness the premises cannot occur, which is exactly what the conclusion says.
--
--   Differences from the source:
--   - generalization: K may change with |I| (p.6); Definition 1 has one (f^φ, g^φ); Boston’s g depends on K → GDA carries K n, f n, g n for each student count n; reason: functions constant in n give one K, f, g, and a family with K depending on |I| and f, g depending on K is the composite with K(n); so the source’s mechanisms are all instances
--   - reading: f^φ, g^φ : ℕ → ℕ with ℕ the positive integers (p.6) → ℕ → ℕ with 0 in the codomain, monotone on the positive integers; reason: the source’s own DA mechanism has g^φ(n) = 0 (p.8)
--   - encoding: finite sets I, S; strict preferences ≻_i over S ∪ {∅} → Fin n, Fin m; injective u i : Option (Fin m) → ℕ, smaller is better; reason: the same instances, for all n, m
--   - encoding: r ∈ [0,1], no tie at a school (p.7) → Tieless r: numbers in the open interval (0,1), injective at each school; reason: footnote 9 says r_is is in (0,1); the boundary is null, every order reachable on [0,1] is reachable on (0,1), and without it Definition 1’s order need not be strict
--   - generalization: reports (ρ_s, r_s) ∈ Γ: ρ_is + r_is ≠ ρ_js + r_js, r ∈ [0,1] (p.13) → ValidReport: numbers in the open interval (0,1), distinct at the school; reason: a subset of Γ, so strategy-proofness in Lean is implied by the source’s and the theorem assumes less; reports in Γ with equal lottery numbers leave Definition 1’s order non-strict and φ undefined
--   - encoding: a preference ≻_s over subsets of I with its weak preference ⪰_s (p.14) → a strict total order pref, with WeakPref := pref ∨ =; reason: a preference is read as a strict total order; a hypothesis over fewer preferences is implied by one over more, and clause (2)–(3) orders are of this kind
--   - generalization: Case 2.b assumes "Without loss of generality" D_is(σ̂(r)) = 0 ≠ 1 = D_is(r) (p.55) → either direction of D_is(σ̂(r)) ≠ D_is(r); reason: the printed direction is the special case; the other direction is not reduced to it on the page and Theorem 1 needs both
--   - encoding: "by the same argument as Case 1" with i″, i* in the roles of i₁(r), i₀(r) (p.57) → the conclusion ¬ StrategyProofForSchools φ; reason: the sentence’s own claim
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), Appendix A.1, Case 2.b, p.57, "Lemmas 9 and 10 imply"

import Definitions.Def_FirstChoiceDesign_IsPivot
import Definitions.Def_FirstChoiceDesign_Swap
import Definitions.Def_FirstChoiceDesign_StrategyProofForSchools

namespace FirstChoiceDesign

/-- The closure of Case 2.b, Cowles Foundation DP No. 2056R, p.57: "Lemmas 9 and 10 imply gDA mechanism `φ` is not
strategy-proof for schools". If `r` is consistent with the regime, `i', i''` are consecutive in
`r_s` within `First_s(r)` with `D_{i' s}(r) = D_{i'' s}(r) = 0`, and `D_is(σ̂(r)) ≠ D_is(r)` for some
`i ∈ First_s(r)`, then `φ` is not strategy-proof for schools.

**Formalization Note** Both directions of `D_is(σ̂(r)) ≠ D_is(r)` are covered: the page's "Without loss
of generality" does not reduce one to the other, and the proof of Theorem 1 needs both. Such a pair
is never the pivot pair, because a pivot pair has different `D`. -/
theorem case_2b_closure {n m : ℕ} (φ : GDA) (X : Problem (φ.K n) n m) (r : Lottery n m)
    (hr : Potential φ.regime r) (s : Fin m) (i i' i'' : Fin n)
    (hc : Consecutive φ X s r i' i'') (h' : ¬ D φ X i' s r) (h'' : ¬ D φ X i'' s r)
    (hi : i ∈ First φ X s r)
    (hne : ¬ (D φ X i s (swapReg φ.regime s i' i'' r) ↔ D φ X i s r)) :
    ¬ StrategyProofForSchools φ := by sorry

end FirstChoiceDesign
