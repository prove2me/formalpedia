-- Prove2me | Theorems.Thm_FirstChoiceDesign_lemma_8
-- name    : FirstChoiceDesign.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:26:43.175198+00:00
-- url     : https://prove2.me/theorems/80cdd796-d7f5-451d-8e17-7eb9ce57b868
-- title:
--   Lemma 8, p.52 — Case 1 yields a profitable manipulation
-- statement:
--   Let $\varphi$ be strategy-proof for schools, and suppose Case 1: $r$ is consistent with the regime, $i_0,i_1$ are the pivots of $r$ at $s$, and $D_{i_0s}(\sigma^*(r))=D_{i_1s}(\sigma^*(r))=0$. Then there exist $(\rho^*,r^*)\in\Gamma^{|S|}$, a preference $\succ_s$ responsive with respect to $(c_s,\rho^*_s,r^*_s)$, and $(\rho'_s,r'_s)\in\Gamma$ such that
--
--   $$
--   \varphi_s((\rho'_s,r'_s),(\rho^*_{-s},r^*_{-s}))\succ_s\varphi_s(\rho^*,r^*).
--   $$
--
--   The conclusion is at the same students, schools, preferences, capacities and school $s$ as $X$.
--
--   Under strategy-proofness the case premises of this item cannot occur, so the hypotheses are jointly unsatisfiable. This is the ordinary shape of a step in a proof by contradiction and not a defect of the formalization.
--
--   Differences from the source:
--   - generalization: K may change with |I| (p.6); Definition 1 has one (f^φ, g^φ); Boston’s g depends on K → GDA carries K n, f n, g n for each student count n; reason: functions constant in n give one K, f, g, and a family with K depending on |I| and f, g depending on K is the composite with K(n); so the source’s mechanisms are all instances
--   - reading: f^φ, g^φ : ℕ → ℕ with ℕ the positive integers (p.6) → ℕ → ℕ with 0 in the codomain, monotone on the positive integers; reason: the source’s own DA mechanism has g^φ(n) = 0 (p.8)
--   - encoding: finite sets I, S; strict preferences ≻_i over S ∪ {∅} → Fin n, Fin m; injective u i : Option (Fin m) → ℕ, smaller is better; reason: the same instances, for all n, m
--   - encoding: r ∈ [0,1], no tie at a school (p.7) → Tieless r: numbers in the open interval (0,1), injective at each school; reason: footnote 9 says r_is is in (0,1); the boundary is null, every order reachable on [0,1] is reachable on (0,1), and without it Definition 1’s order need not be strict
--   - generalization: reports (ρ_s, r_s) ∈ Γ: ρ_is + r_is ≠ ρ_js + r_js, r ∈ [0,1] (p.13) → ValidReport: numbers in the open interval (0,1), distinct at the school; reason: a subset of Γ, so strategy-proofness in Lean is implied by the source’s and the theorem assumes less; reports in Γ with equal lottery numbers leave Definition 1’s order non-strict and φ undefined
--   - encoding: a preference ≻_s over subsets of I with its weak preference ⪰_s (p.14) → a strict total order pref, with WeakPref := pref ∨ =; reason: a preference is read as a strict total order; a hypothesis over fewer preferences is implied by one over more, and clause (2)–(3) orders are of this kind
--   - reading: the statement does not mention strategy-proofness → hypothesis StrategyProofForSchools φ; reason: standing assumption of the proof: "If φ is not strategy-proof for schools, then the proof of Theorem 1 is complete" (p.51; likewise p.56)
--   - encoding: the case i₀(r) = i₁(r) = ∅, where the permutations are the identity → a pivot pair is a hypothesis; reason: in the omitted case the claim is trivial or has no meaning
--   - reading: the lemma states no hypothesis beyond the proof’s context → Case 1 as hypotheses: r Potential, a pivot pair, both rejected at σ*(r); reason: the proof opens "Lemmas 5, 6, and 7 imply that there exists r" in Case 1 (p.52)
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), Lemma 8, p.52; Case 1, p.50

import Definitions.Def_FirstChoiceDesign_IsPivot
import Definitions.Def_FirstChoiceDesign_Swap
import Definitions.Def_FirstChoiceDesign_StrategyProofForSchools

namespace FirstChoiceDesign

/-- Lemma 8 (existence of a profitable preference manipulation), Cowles Foundation DP No. 2056R, p.52. In Case 1
(p.50: a profile `r` consistent with the regime with `D_{i₀(r) s}(σ*(r)) = D_{i₁(r) s}(σ*(r)) = 0`) there
exist `(ρ*, r*) ∈ Γ^{|S|}`, a preference `≻_s` responsive with respect to `(c_s, ρ*_s, r*_s)`, and
`(ρ'_s, r'_s) ∈ Γ` such that `φ_s((ρ'_s, r'_s), (ρ*_{-s}, r*_{-s})) ≻_s φ_s(ρ*, r*)`.

**Formalization Note** The hypothesis `StrategyProofForSchools φ` is the standing assumption of the
proof, which treats the other case as already finished ("If `φ` is not strategy-proof for schools,
then the proof of Theorem 1 is complete", p.51). The case premises of this item are steps of a proof by contradiction: under strategy-proofness they cannot occur, so the item holds with a hypothesis no instance meets. That is the shape of the argument and not a defect of the encoding.

The conclusion is the printed existential, at the same `(I, S, ≻_I, (c_s)_{s ∈ S})` and school `s`. -/
theorem lemma_8 (φ : GDA) (hφ : StrategyProofForSchools φ) {n m : ℕ} (X : Problem (φ.K n) n m)
    (r : Lottery n m) (hr : Potential φ.regime r) (s : Fin m) (i₀ i₁ : Fin n)
    (hp : IsPivot φ X s r i₀ i₁) (h₀ : ¬ D φ X i₀ s (swapReg φ.regime s i₀ i₁ r))
    (h₁ : ¬ D φ X i₁ s (swapReg φ.regime s i₀ i₁ r)) :
    ∃ (ρs : Fin n → Fin m → ℕ) (rs : Lottery n m) (pref : Finset (Fin n) → Finset (Fin n) → Prop)
      (ρ' : Fin n → ℕ) (r' : Fin n → ℝ),
      (∀ t, ValidReport (φ.K n) (ρs · t) (rs · t)) ∧ IsStrictTotalOrder _ pref ∧
        Responsive (X.c s) (fun i => (ρs i s : ℝ) + rs i s) pref ∧
        ValidReport (φ.K n) ρ' r' ∧
        pref (assigned φ X.toSetting (updateColumn s ρ' ρs) (updateColumn s r' rs) s)
          (assigned φ X.toSetting ρs rs s) := by sorry

end FirstChoiceDesign
