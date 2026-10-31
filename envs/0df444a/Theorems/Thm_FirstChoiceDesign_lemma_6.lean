-- Prove2me | Theorems.Thm_FirstChoiceDesign_lemma_6
-- name    : FirstChoiceDesign.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:26:33.805988+00:00
-- url     : https://prove2.me/theorems/8c841344-4c5f-4837-bbec-0c0e7328fe09
-- title:
--   Lemma 6, p.50 — outcome equivalence between $r$ and $(r^*_s,\tilde\sigma_{-s}(r))$
-- statement:
--   Let $\varphi$ be strategy-proof for schools and let $i_0,i_1$ be the pivots of $r$ at $s$. With $r^*_s$ and $\tilde\sigma_{-s}(r)\equiv(\tilde\sigma_{s'}(r))_{s'\ne s}$ as defined on p.50,
--
--   $$
--   \varphi(r)=\varphi(r^*_s,\tilde\sigma_{-s}(r)),
--   $$
--
--   and therefore $D_{i_0s}(r^*_s,\tilde\sigma_{-s}(r))=0$ and $D_{i_1s}(r^*_s,\tilde\sigma_{-s}(r))=1$.
--
--   Read without strategy-proofness the printed statement is false. Under the DA mechanism with MTB, $K=2$, $A$ of capacity 1, $B$ of capacity 2 and $s=B$, take $a:A,B,\emptyset$; $b:B,\emptyset$; $c:A,B,\emptyset$; $d:B,A,\emptyset$; $\rho_A$: $c=d=1$, $a=b=2$; $\rho_B$ all equal; lottery order at $A$: $d,a,b,c$; at $B$: $b,c,a,d$. DA gives $A=\{d\}$, $B=\{b,c\}$, with pivots $i_1=b$, $i_0=d$, and at $(r^*_B,r_A)$ DA gives $A=\{c\}$, $B=\{b,d\}$.
--
--   Differences from the source:
--   - generalization: K may change with |I| (p.6); Definition 1 has one (f^φ, g^φ); Boston’s g depends on K → GDA carries K n, f n, g n for each student count n; reason: functions constant in n give one K, f, g, and a family with K depending on |I| and f, g depending on K is the composite with K(n); so the source’s mechanisms are all instances
--   - reading: f^φ, g^φ : ℕ → ℕ with ℕ the positive integers (p.6) → ℕ → ℕ with 0 in the codomain, monotone on the positive integers; reason: the source’s own DA mechanism has g^φ(n) = 0 (p.8)
--   - encoding: finite sets I, S; strict preferences ≻_i over S ∪ {∅} → Fin n, Fin m; injective u i : Option (Fin m) → ℕ, smaller is better; reason: the same instances, for all n, m
--   - encoding: r ∈ [0,1], no tie at a school (p.7) → Tieless r: numbers in the open interval (0,1), injective at each school; reason: footnote 9 says r_is is in (0,1); the boundary is null, every order reachable on [0,1] is reachable on (0,1), and without it Definition 1’s order need not be strict
--   - generalization: reports (ρ_s, r_s) ∈ Γ: ρ_is + r_is ≠ ρ_js + r_js, r ∈ [0,1] (p.13) → ValidReport: numbers in the open interval (0,1), distinct at the school; reason: a subset of Γ, so strategy-proofness in Lean is implied by the source’s and the theorem assumes less; reports in Γ with equal lottery numbers leave Definition 1’s order non-strict and φ undefined
--   - encoding: a preference ≻_s over subsets of I with its weak preference ⪰_s (p.14) → a strict total order pref, with WeakPref := pref ∨ =; reason: a preference is read as a strict total order; a hypothesis over fewer preferences is implied by one over more, and clause (2)–(3) orders are of this kind
--   - reading: the statement does not mention strategy-proofness → hypothesis StrategyProofForSchools φ; reason: standing assumption of the proof: "If φ is not strategy-proof for schools, then the proof of Theorem 1 is complete" (p.51; likewise p.56)
--   - encoding: any lottery number profile r → Tieless r, not required Consistent with the regime; reason: the proof of Theorem 1 uses the statement at such profiles; consistent profiles are a special case
--   - encoding: the case i₀(r) = i₁(r) = ∅, where the permutations are the identity → a pivot pair is a hypothesis; reason: in the omitted case the claim is trivial or has no meaning
--   - encoding: r*_s, σ̃_s′(r) defined by their conditions → universally quantified columns satisfying IsRStar, IsSigmaTilde; reason: the conditions determine the columns (σ̃ up to its order)
--   - reading: σ̃_{i₁ s′}(r) = max{r_is′ | r_is′ < r_{i₀ s′}} (p.50) → "moving i₁(r) to right above i₀(r)" as an order condition on a permutation of r_s′; reason: the formula is undefined when i₀ has the smallest number at s′ and collides with a predecessor’s number; mechanisms use only the order
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), Lemma 6, p.50

import Definitions.Def_FirstChoiceDesign_IsPivot
import Definitions.Def_FirstChoiceDesign_IsRStar
import Definitions.Def_FirstChoiceDesign_Swap
import Definitions.Def_FirstChoiceDesign_StrategyProofForSchools

namespace FirstChoiceDesign

/-- Lemma 6 (outcome equivalence between `r` and `(r*_s, σ̃_{-s}(r))`), Cowles Foundation DP No. 2056R, p.50. For all
`r`, `φ(r) = φ(r*_s, σ̃_{-s}(r))`, and therefore `D_{i₀(r) s}(r*_s, σ̃_{-s}(r)) = 0` and
`D_{i₁(r) s}(r*_s, σ̃_{-s}(r)) = 1` whenever `i₀(r), i₁(r) ≠ ∅`.

**Formalization Note** The hypothesis `StrategyProofForSchools φ` is the standing assumption of the
proof, which treats the other case as already finished ("If `φ` is not strategy-proof for schools,
then the proof of Theorem 1 is complete", p.51). Without it the printed lemma fails, under the DA mechanism. When no pivot pair exists, `r* = r` and `σ̃ = r`, and the claim is trivial. -/
theorem lemma_6 (φ : GDA) (hφ : StrategyProofForSchools φ) {n m : ℕ} (X : Problem (φ.K n) n m)
    (r : Lottery n m) (hr : Tieless r) (s : Fin m) (i₀ i₁ : Fin n)
    (hp : IsPivot φ X s r i₀ i₁) (c : Fin n → ℝ) (hc : IsRStar φ X s r i₀ i₁ c)
    (τ : Lottery n m) (hτ : IsSigmaTilde φ.regime s r i₀ i₁ τ) :
    outcome φ X.toSetting X.ρ r = outcome φ X.toSetting X.ρ (updateColumn s c τ) ∧
      ¬ D φ X i₀ s (updateColumn s c τ) ∧ D φ X i₁ s (updateColumn s c τ) := by sorry

end FirstChoiceDesign
