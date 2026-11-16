-- Prove2me | Theorems.Thm_BirthdayEntropy_Soundness_Supplement_lemma_B_2
-- name    : BirthdayEntropy.Soundness.Supplement.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:23:14.921832+00:00
-- url     : https://prove2.me/theorems/a9ee9b22-bfc6-4967-b99d-460d04a975ab
-- title:
--   Lemma B.2 — Robust ternary clause exposure
-- statement:
--   Fix a global assignment $g$ to an indexed Boolean ternary CSP, and a family $J$ of $t\ge\gamma n$ constraints violated by $g$, with pairwise disjoint three-variable scopes. Let $0<\gamma\le1/3$ and $2\le\ell\le\sqrt n$. Orient each scope as $(a_j,b_j,c_j)$ arbitrarily. Sample $S,T$ independently and uniformly from all $K=\binom n\ell$ views with replacement. Set $\alpha=\ell(\ell-1)/(n(n-1))$, $\Lambda=t\alpha$, $p_0=(\ell/n)\Lambda$, and $X=\sum_{j\in J}\mathbf1\{c_j\in S,\ a_j,b_j\in T\}$. For any $f\ge0$ and any bad-view set $B$ with $|B|\le fK$, put $Y=X\mathbf1\{S,T\notin B\}$. Then
--
--   $$\mathbb EX=p_0,\qquad\mathbb EX^2\le p_0+p_0^2,$$
--   $$\mathbb EY\ge p_0\left(1-\frac f\gamma-\sqrt{\frac{f(1+\Lambda)}\Lambda}\right).$$
--
--   If additionally $f\le\gamma\Lambda/200$, then
--
--   $$\mathbb P(Y>0)\ge\frac38p_0\ge\frac{3\gamma\ell^3}{16n^2}.$$
--
--   The bad-view events need not be independent of $X$. This full exposure estimate supports Theorem B.3 and does not assume that theorem's threshold $n\ge16/\gamma$.
--
--   Differences from the source:
--   - encoding: 2 <= ell <= sqrt(n) → natural-number ell with 2 <= ell and ell^2 <= n; reason: these conditions are equivalent on nonnegative integers
--   - encoding: oriented violated disjoint triples and independent uniform views → indexed constraint set, arbitrary scope permutations, and normalized sums over all ordered view pairs; reason: constraint rows have distinct coordinates and every orientation is permitted; the bad set remains adversarial
-- source:
--   Alexandru Popa, STOC 2027 submission #907 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/907.pdf, Lemma B.2, PDF p23 / printed p22; proof continues PDF p24 / printed p23

import Mathlib
import Definitions.Def_BirthdayEntropy_Soundness_Supplement_Exposure

namespace BirthdayEntropy.Soundness.Supplement

/-- Lemma B.2, (30)–(32), PDF pp23–24 / printed pp22–23. No n≥16/gamma
threshold is imposed. Integer ell²≤n encodes the printed ell≤sqrt(n). -/
theorem lemma_B_2 (n m ℓ : ℕ) (φ : CSP n m) (g : Fin n → Bool)
    (J : Finset (Fin m)) (o : Fin m → Equiv.Perm (Fin 3))
    (γ f : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1/3)
    (hℓ : 2 ≤ ℓ) (hℓn : ℓ^2 ≤ n)
    (hJ : DisjointViolations φ g J) (ht : γ * n ≤ (J.card : ℝ))
    (hf : 0 ≤ f) (B : Finset (View n ℓ)) (hB : (B.card : ℝ) ≤ f * Nat.choose n ℓ) :
    let Λ := exposureLambda n ℓ J
    let p₀ := exposureP0 n ℓ J
    let X := exposureX (ℓ := ℓ) φ J o
    let Y := exposureY φ J o B
    viewPairMean X = p₀ ∧
    viewPairMean (fun S T => (X S T)^2) ≤ p₀ + p₀^2 ∧
    p₀ * (1 - f / γ - Real.sqrt (f * (1 + Λ) / Λ)) ≤ viewPairMean Y ∧
    (f ≤ γ * Λ / 200 →
      (3/8 : ℝ) * p₀ ≤ viewPairProb (fun S T => 0 < Y S T) ∧
      3 * γ * (ℓ : ℝ)^3 / (16 * (n : ℝ)^2) ≤ (3/8 : ℝ) * p₀) := by sorry

end BirthdayEntropy.Soundness.Supplement
