-- Prove2me | Theorems.Thm_FirstChoiceDesign_lemma_3
-- name    : FirstChoiceDesign.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:26:13.539106+00:00
-- url     : https://prove2.me/theorems/720a7b8e-ec89-422d-b749-9108d0a1d1b8
-- title:
--   Lemma 3, p.41 — under strategy-proofness, a switch below the cutoff changes nothing
-- statement:
--   Let $X$ be an assignment problem, $r$ a lottery number profile and $\varphi$ a gDA mechanism that is strategy-proof for schools. Let $\delta_s(r)$ switch only $i'$ and $i''$, with $\rho^\varphi_{i's}=\rho^\varphi_{i''s}$ and $\min\{\rho^\varphi_{i's}+r_{i's},\rho^\varphi_{i''s}+r_{i''s}\}>\rho^\varphi_{is}+r_{is}$ for all $i$ with $D_{is}(r)=1$. Then
--
--   $$
--   \varphi(r)=\varphi(\delta_s(r),r_{-s}).
--   $$
--
--   The lemma fails without strategy-proofness. It says that the order among equal-priority students behind the cutoff has no effect on the assignment.
--
--   **Formalization Note** The switch happens at school $s$ only, under either regime, and $r$ need not be consistent with the regime.
--
--   Differences from the source:
--   - generalization: K may change with |I| (p.6); Definition 1 has one (f^φ, g^φ); Boston’s g depends on K → GDA carries K n, f n, g n for each student count n; reason: functions constant in n give one K, f, g, and a family with K depending on |I| and f, g depending on K is the composite with K(n); so the source’s mechanisms are all instances
--   - reading: f^φ, g^φ : ℕ → ℕ with ℕ the positive integers (p.6) → ℕ → ℕ with 0 in the codomain, monotone on the positive integers; reason: the source’s own DA mechanism has g^φ(n) = 0 (p.8)
--   - encoding: finite sets I, S; strict preferences ≻_i over S ∪ {∅} → Fin n, Fin m; injective u i : Option (Fin m) → ℕ, smaller is better; reason: the same instances, for all n, m
--   - encoding: r ∈ [0,1], no tie at a school (p.7) → Tieless r: numbers in the open interval (0,1), injective at each school; reason: footnote 9 says r_is is in (0,1); the boundary is null, every order reachable on [0,1] is reachable on (0,1), and without it Definition 1’s order need not be strict
--   - generalization: reports (ρ_s, r_s) ∈ Γ: ρ_is + r_is ≠ ρ_js + r_js, r ∈ [0,1] (p.13) → ValidReport: numbers in the open interval (0,1), distinct at the school; reason: a subset of Γ, so strategy-proofness in Lean is implied by the source’s and the theorem assumes less; reports in Γ with equal lottery numbers leave Definition 1’s order non-strict and φ undefined
--   - encoding: a preference ≻_s over subsets of I with its weak preference ⪰_s (p.14) → a strict total order pref, with WeakPref := pref ∨ =; reason: a preference is read as a strict total order; a hypothesis over fewer preferences is implied by one over more, and clause (2)–(3) orders are of this kind
--   - encoding: any lottery number profile r → Tieless r, not required Consistent with the regime; reason: the proof of Theorem 1 uses the statement at such profiles; consistent profiles are a special case
--   - encoding: "If there are no such i′ and i″, let δ_s(r) be the same as r_s" → not stated; i′, i″ are hypotheses; reason: the omitted case is the identity
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), Lemma 3, p.41

import Definitions.Def_FirstChoiceDesign_BelowCutoff
import Definitions.Def_FirstChoiceDesign_Swap
import Definitions.Def_FirstChoiceDesign_StrategyProofForSchools

namespace FirstChoiceDesign

/-- Lemma 3, Cowles Foundation DP No. 2056R, p.41. If `φ` is strategy-proof for schools and `δ_s(r)` switches
only `i'` and `i''` in `r_s`, with `ρ^φ_i's = ρ^φ_i''s` and
`min{ρ^φ_i's + r_i's, ρ^φ_i''s + r_i''s} > ρ^φ_is + r_is` for all `i` with `D_is(r) = 1`, then
`φ(r) = φ(δ_s(r), r_{-s})`.

**Formalization Note** `r` need not be consistent with the regime: the switch is at school `s` only,
under either regime, and the proof of Theorem 1 applies the lemma at such profiles. -/
theorem lemma_3 (φ : GDA) (hφ : StrategyProofForSchools φ) {n m : ℕ} (X : Problem (φ.K n) n m)
    (r : Lottery n m) (hr : Tieless r) (s : Fin m) (i' i'' : Fin n)
    (hδ : BelowCutoff φ X s r i' i'') :
    outcome φ X.toSetting X.ρ r = outcome φ X.toSetting X.ρ (swapAt s i' i'' r) := by sorry

end FirstChoiceDesign
