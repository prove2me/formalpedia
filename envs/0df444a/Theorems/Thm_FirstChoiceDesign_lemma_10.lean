-- Prove2me | Theorems.Thm_FirstChoiceDesign_lemma_10
-- name    : FirstChoiceDesign.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:28:23.185241+00:00
-- url     : https://prove2.me/theorems/bc0615bc-c6a5-4b10-93ae-c72f11159a3c
-- title:
--   Lemma 10, p.56 — in Case 2.b, a switch of $i^*$ and $i''$ moves the seat to $i''$
-- statement:
--   In the setting of Lemma 9, let $\hat\sigma^{\#\#}_s(r)$ be the permutation of $\hat\sigma^\#_s(r)$ that switches $i^*$ and $i''$. Then
--
--   $$
--   D_{i^*s}(\hat\sigma^{\#\#}_s(r),\hat\sigma_{-s}(r))=0\quad\text{and}\quad D_{i''s}(\hat\sigma^{\#\#}_s(r),\hat\sigma_{-s}(r))=1.
--   $$
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
--   - encoding: the two "Without loss of generality" normalizations of Case 2.b → hypotheses r_i′s < r_i″s and D_is(σ̂(r)) = 0 ≠ 1 = D_is(r) in Case2b; reason: the printed situation of Lemmas 9, 10; case_2b_closure covers the other direction
--   - encoding: "change i*’s preference" with order among s′ ≠ s unspecified (p.55) → any X′ with IsTruncation X X′ iStar s; the situation is stated in X, σ̂^# and the conclusion in X′; reason: the source leaves the order free; the statement covers all choices
--   - encoding: σ̂^#_s(r) defined by its conditions → universally quantified column satisfying IsSigmaSharp; reason: the conditions determine the column
--   - reading: σ̂₋ₛ(r) ≡ (σ̂_s′(r))_{s′∈S} (p.55) → the columns s′ ≠ s of swapReg, via updateColumn; reason: s′ ≠ s is meant; column s is replaced by the sharp column
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), Lemma 10, p.56; Case 2.b, p.55

import Definitions.Def_FirstChoiceDesign_Case2b
import Definitions.Def_FirstChoiceDesign_StrategyProofForSchools

namespace FirstChoiceDesign

/-- Lemma 10, Cowles Foundation DP No. 2056R, p.56. In Case 2.b, on the problem with `i*`'s preference changed,
`D_{i* s}(σ̂^##_s(r), σ̂_{-s}(r)) = 0` and `D_{i'' s}(σ̂^##_s(r), σ̂_{-s}(r)) = 1`.

**Formalization Note** The hypothesis `StrategyProofForSchools φ` is the standing assumption of the
proof, which treats the other case as already finished ("If `φ` is not strategy-proof for schools,
then the proof of Theorem 1 is complete", p.51). The case premises of this item are steps of a proof by contradiction: under strategy-proofness they cannot occur, so the item holds with a hypothesis no instance meets. That is the shape of the argument and not a defect of the encoding.

`σ̂^##_s(r)` is the column `σ̂^#_s(r)` with the numbers of `i*` and `i''` switched, p.56. -/
theorem lemma_10 (φ : GDA) (hφ : StrategyProofForSchools φ) {n m : ℕ}
    (X X' : Problem (φ.K n) n m) (r : Lottery n m) (hr : Potential φ.regime r) (s : Fin m)
    (i i' i'' iStar : Fin n) (hcase : Case2b φ X s r i i' i'' iStar)
    (hX' : IsTruncation X X' iStar s) (c : Fin n → ℝ) (hc : IsSigmaSharp φ X' s r i' i'' c) :
    ¬ D φ X' iStar s
        (updateColumn s (fun j => c (Equiv.swap iStar i'' j)) (swapReg φ.regime s i' i'' r)) ∧
      D φ X' i'' s
        (updateColumn s (fun j => c (Equiv.swap iStar i'' j)) (swapReg φ.regime s i' i'' r)) := by sorry

end FirstChoiceDesign
