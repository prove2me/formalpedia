-- Prove2me | Theorems.Thm_FirstChoiceDesign_lemma_5
-- name    : FirstChoiceDesign.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:26:23.067789+00:00
-- url     : https://prove2.me/theorems/0ecb05af-c224-4d4a-9dc2-376486a66728
-- title:
--   Lemma 5, p.47 — failure of the design breaks the Fisher property
-- statement:
--   Suppose the first-choice research design does not extract a random assignment for $\varphi$ at school $s$ and problem $X$: there are a potential realization and $j,k$ in its first-choice set with different probabilities of assignment to $s$. Then there exists a lottery number profile $r$ consistent with the regime satisfying the following: either
--
--   $$
--   D_{i_0(r)s}(\sigma^*(r))=D_{i_1(r)s}(\sigma^*(r))=0,
--   $$
--
--   or there exist some student $i\in\mathit{First}_s(r)$ and some permutation $\hat\sigma_s(r)$, switching two students consecutive in $r_s$ within $\mathit{First}_s(r)$ other than the pivot pair, such that $D_{is}(\hat\sigma(r))\ne D_{is}(r)$.
--
--   No strategy-proofness is assumed. The lemma reduces a statement about probabilities to one about single switches of lottery numbers. It is the only milestone that mentions the law of $R$.
--
--   Differences from the source:
--   - generalization: K may change with |I| (p.6); Definition 1 has one (f^φ, g^φ); Boston’s g depends on K → GDA carries K n, f n, g n for each student count n; reason: functions constant in n give one K, f, g, and a family with K depending on |I| and f, g depending on K is the composite with K(n); so the source’s mechanisms are all instances
--   - reading: f^φ, g^φ : ℕ → ℕ with ℕ the positive integers (p.6) → ℕ → ℕ with 0 in the codomain, monotone on the positive integers; reason: the source’s own DA mechanism has g^φ(n) = 0 (p.8)
--   - encoding: finite sets I, S; strict preferences ≻_i over S ∪ {∅} → Fin n, Fin m; injective u i : Option (Fin m) → ℕ, smaller is better; reason: the same instances, for all n, m
--   - encoding: r ∈ [0,1], no tie at a school (p.7) → Tieless r: numbers in the open interval (0,1), injective at each school; reason: footnote 9 says r_is is in (0,1); the boundary is null, every order reachable on [0,1] is reachable on (0,1), and without it Definition 1’s order need not be strict
--   - reading: the lemma states no hypothesis → hfail: extraction fails at X and s; reason: running supposition of "Main Proof": "Fix φ, s, and X throughout" (p.45)
--   - encoding: D_{i₀(r)s}(σ*(r)) = D_{i₁(r)s}(σ*(r)) = 0, for pivots that may be ∅ → the first disjunct asserts that a pivot pair exists; reason: D of ∅ has no meaning; σ*(r) = r otherwise
--   - encoding: σ̂_s(r) ≠ σ*_s(r), or σ̂_s(r) = r_s if no pair exists (p.46) → a consecutive pair that is neither (i₀, i₁) nor (i₁, i₀); reason: the no-op clause cannot change D
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), Lemma 5, p.47; Main Proof, p.45

import Definitions.Def_FirstChoiceDesign_IsPivot
import Definitions.Def_FirstChoiceDesign_Swap
import Definitions.Def_FirstChoiceDesign_lotteryLaw

namespace FirstChoiceDesign

/-- Lemma 5 (a breakdown of the Fisher property), Cowles Foundation DP No. 2056R, p.47. Under the running
supposition of "Main Proof", p.45, that the design does not extract a random assignment for `φ` at
`s` and `X`, there exists a profile `r` consistent with the regime satisfying the following:
`D_{i₀(r) s}(σ*(r)) = D_{i₁(r) s}(σ*(r)) = 0`, or there exist some `i ∈ First_s(r)` and some permutation
`σ̂_s(r)` such that `D_is(σ̂(r)) ≠ D_is(r)`.

**Formalization Note** `swapReg` is `σ*` or `σ̂`. The first disjunct requires a pivot pair to exist:
if none does, `σ*(r) = r` and the page's `D_{∅ s}` has no meaning. In the second, `σ̂_s(r)` is the switch
of a pair `i', i''` consecutive in `r_s` within `First_s(r)` that is not the pivot pair, which is the
page's `σ̂_s(r) ≠ σ*_s(r)`. Its no-op clause cannot change `D`. -/
theorem lemma_5 {n m : ℕ} (φ : GDA) (X : Problem (φ.K n) n m) (s : Fin m)
    (hfail : ¬ ∀ r : Lottery n m, Potential φ.regime r →
      ∀ j ∈ First φ X s r, ∀ k ∈ First φ X s r,
        lotteryLaw (n := n) (m := m) φ.regime {R | D φ X j s R} =
          lotteryLaw (n := n) (m := m) φ.regime {R | D φ X k s R}) :
    ∃ r : Lottery n m, Potential φ.regime r ∧
      ((∃ i₀ i₁, IsPivot φ X s r i₀ i₁ ∧
          ¬ D φ X i₀ s (swapReg φ.regime s i₀ i₁ r) ∧ ¬ D φ X i₁ s (swapReg φ.regime s i₀ i₁ r)) ∨
        ∃ i i' i'', i ∈ First φ X s r ∧ Consecutive φ X s r i' i'' ∧
          ¬ IsPivot φ X s r i' i'' ∧ ¬ IsPivot φ X s r i'' i' ∧
          ¬ (D φ X i s (swapReg φ.regime s i' i'' r) ↔ D φ X i s r)) := by sorry

end FirstChoiceDesign
