-- Prove2me | Theorems.Thm_AgreementTop736_Exact_eq3_conditioned_gap
-- name    : AgreementTop736.Exact.eq3_conditioned_gap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:14.770196+00:00
-- url     : https://prove2.me/theorems/b8107fce-e353-4f56-890d-a5b40c836939
-- title:
--   Section 3.1, eq. (3) — $\mathbb E_{H,K,K'|x\in H}(\varphi_{x,s}(K)-\varphi_{x,s}(K'))^2\ge\gamma\,\mathbb E_{K|x}\varphi_{x,s}(K)^2$
-- statement:
--   Let the sampling scheme satisfy hypothesis 1 of Theorem 7 (uniform inclusion probability $\rho$) and hypothesis 3 (every element-conditioned walk $M_x$, $x$ of positive marginal mass, has spectral gap at least $\gamma>0$). Let $F$ be local functions into a finite alphabet, $g$ a coordinatewise majority, $a>0$, $x$ an element of positive marginal mass and $s\ne g(x)$. Then, with $(H,K,K')$ distributed as in the agreement test and conditioned on $x\in H$,
--   $$\mathbb E_{H,K,K'\mid x\in H}\big(\varphi_{x,s}(K)-\varphi_{x,s}(K')\big)^2\ \ge\ \gamma\,\mathbb E_{K|x}\varphi_{x,s}(K)^2 .$$
--
--   Summed over element–label pairs this gives the lower bound (5) on the weighted non-polarity.
--
--   **Formalization Note** The conditional expectation is the test-weighted sum restricted to $x\in H$, divided by $P[x\in H]=\sum_H\mu_H(H)\mathbf 1[x\in H]$, which is positive under the hypotheses.
--
--   Differences from the source:
--   - generalization: conditions on the downward kernel and hypotheses 1–2 stated for each top set K → required only for top sets K with μ(K) > 0; reason: §1.1 (p.4) states them for every K of positive mass and §2 (p.7) omits faces of zero mass; the Lean hypotheses are implied by the printed ones
--   - encoding: local functions F_K : K → Σ → F : Finset V → V → α, with every comparison restricted to x ∈ K (resp. x ∈ H); reason: values F K x with x ∉ K never enter any statement; same instances
--   - encoding: probabilities and expectations under μ, D(·|K), U(·|H), μ(·|x ∈ K) → finite weighted sums; U(K|H) = μ(K)D(H|K)/μ_H(H) and μ_x(K) = μ(K)1[x∈K]/P[x∈K] with the convention t/0 = 0; reason: the model is finite; the convention only affects terms of zero weight
--   - encoding: M_x has spectral gap γ_x = 1 − λ₂(M_x) ≥ γ → Poincaré inequality γ Var_{μ_x}(f) ≤ ½ E_{K∼μ_x, K'∼M_x(K,·)}(f(K) − f(K'))² for every real f on top sets; reason: the paper's own displayed form of the gap (§1.1, p.4); equivalent for the reversible M_x (reversible under hypothesis 1, p.8), and the proof uses only this form
--   - encoding: H sampled from D(·|K) conditioned on x ∈ H → weight D(H|K)1[x∈H]/P_{H∼D(·|K)}[x∈H]; reason: the definition of conditioning; under hypothesis 1 the denominator is ρ > 0 for every K ∋ x of positive mass
--   - encoding: E_{H,K,K'|x∈H} → (∑_{H,K,K'} μ_H(H)U(K|H)U(K'|H)1[x∈H](φ(K)−φ(K'))²) / P[x∈H]; reason: the definition of conditional expectation; the denominator is positive for x of positive mass under hypothesis 1
--   - generalization: a step of the proof of Theorem 7, under all hypotheses of Theorem 7 → the standing model, hypotheses 1 and 3, and a coordinatewise majority g (no hypothesis 2); reason: the step uses only these hypotheses; the Lean statement specializes to the source's setting
-- source:
--   Tali Kaufman, Huy Tuan Pham, Exact Agreement Expansion up to the Top via Non-polarity, STOC 2027 submission #736 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/736.pdf (source.pdf sha256 04ba433ef4a669f9160de90c29bfff3152be2a1d08e50186f52e514c298f5d49), p.10, Section 3.1, eq. (3)

import Mathlib
import Definitions.Def_AgreementTop736_Exact_Regularized

namespace AgreementTop736.Exact

open Finset Scheme

/-- §3.1, eq. (3), p.10: under hypotheses 1 and 3 of Theorem 7, for an element `x` of positive
marginal mass, `s ≠ g(x)` with `g` a coordinatewise majority, and `a > 0`,
`E_{H,K,K' | x ∈ H} (φ_{x,s}(K) − φ_{x,s}(K'))² ≥ γ E_{K|x} φ_{x,s}(K)²`, where the left side is the
expectation under the agreement test's joint law conditioned on `x ∈ H`. -/
theorem eq3_conditioned_gap {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Fintype α] [DecidableEq α]
    (S : Scheme V) (hS : S.IsValid) (h1 : S.UniformInclusion) {γ : ℝ} (hγ : 0 < γ)
    (h3 : S.HasConditionedGap γ) (F : Finset V → V → α) (g : V → α)
    (hg : S.IsCoordMajority F g) {a : ℝ} (ha : 0 < a) (x : V) (hx : 0 < S.pointMass x)
    (s : α) (hs : s ≠ g x) :
    γ * ∑ K, S.μx x K * phi F g a x s K ^ 2 ≤
      (∑ H, ∑ K, ∑ K', S.testWeight H K K' * (if x ∈ H then 1 else 0) *
          (phi F g a x s K - phi F g a x s K') ^ 2) / S.probInH x := by sorry

end AgreementTop736.Exact
