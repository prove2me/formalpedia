-- Prove2me | Theorems.Thm_FirstChoiceDesign_lemma_4
-- name    : FirstChoiceDesign.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:26:37.535192+00:00
-- url     : https://prove2.me/theorems/48c8bcd6-b353-44ff-981b-afa90e8988db
-- title:
--   Lemma 4, p.43 — a switch at or above the cutoff changes nothing
-- statement:
--   Let $X$ be an assignment problem, $r$ a lottery number profile and $\varphi$ any gDA mechanism. Let $\delta_s(r)$ switch only two students $i'$ and $i''$ with $\rho^\varphi_{i's}=\rho^\varphi_{i''s}$, and suppose there exists $i$ with $D_{is}(r)=1$ such that $\max\{\rho^\varphi_{i's}+r_{i's},\rho^\varphi_{i''s}+r_{i''s}\}\le\rho^\varphi_{is}+r_{is}$. Then
--
--   $$
--   \varphi(r)=\varphi(\delta_s(r),r_{-s}).
--   $$
--
--   No strategy-proofness is needed. The lemma is the counterpart of Lemma 3 for students at or ahead of the cutoff.
--
--   Differences from the source:
--   - generalization: K may change with |I| (p.6); Definition 1 has one (f^φ, g^φ); Boston’s g depends on K → GDA carries K n, f n, g n for each student count n; reason: functions constant in n give one K, f, g, and a family with K depending on |I| and f, g depending on K is the composite with K(n); so the source’s mechanisms are all instances
--   - reading: f^φ, g^φ : ℕ → ℕ with ℕ the positive integers (p.6) → ℕ → ℕ with 0 in the codomain, monotone on the positive integers; reason: the source’s own DA mechanism has g^φ(n) = 0 (p.8)
--   - encoding: finite sets I, S; strict preferences ≻_i over S ∪ {∅} → Fin n, Fin m; injective u i : Option (Fin m) → ℕ, smaller is better; reason: the same instances, for all n, m
--   - encoding: r ∈ [0,1], no tie at a school (p.7) → Tieless r: numbers in the open interval (0,1), injective at each school; reason: footnote 9 says r_is is in (0,1); the boundary is null, every order reachable on [0,1] is reachable on (0,1), and without it Definition 1’s order need not be strict
--   - encoding: any lottery number profile r → Tieless r, not required Consistent with the regime; reason: the proof of Theorem 1 uses the statement at such profiles; consistent profiles are a special case
--   - encoding: "If there are no such i′ and i″, let δ_s(r) be the same as r_s" → not stated; i′, i″ are hypotheses; reason: the omitted case is the identity
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), Lemma 4, p.43

import Definitions.Def_FirstChoiceDesign_BelowCutoff
import Definitions.Def_FirstChoiceDesign_Swap

namespace FirstChoiceDesign

/-- Lemma 4, Cowles Foundation DP No. 2056R, p.43. If `δ_s(r)` switches only `i'` and `i''` in `r_s`, with
`ρ^φ_i's = ρ^φ_i''s`, and there exists `i` with `D_is(r) = 1` such that
`max{ρ^φ_i's + r_i's, ρ^φ_i''s + r_i''s} ≤ ρ^φ_is + r_is`, then `φ(r) = φ(δ_s(r), r_{-s})`. -/
theorem lemma_4 {n m : ℕ} (φ : GDA) (X : Problem (φ.K n) n m) (r : Lottery n m) (hr : Tieless r)
    (s : Fin m) (i' i'' : Fin n) (hδ : AboveCutoff φ X s r i' i'') :
    outcome φ X.toSetting X.ρ r = outcome φ X.toSetting X.ρ (swapAt s i' i'' r) := by sorry

end FirstChoiceDesign
