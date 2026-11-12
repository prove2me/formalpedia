-- Prove2me | Theorems.Thm_AgreementTop736_Exact_sec3_1_cauchy_schwarz_variance
-- name    : AgreementTop736.Exact.sec3_1_cauchy_schwarz_variance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:08.666265+00:00
-- url     : https://prove2.me/theorems/71429731-2562-446d-93a8-442e1abd5fc6
-- title:
--   Section 3.1, p.10 — Cauchy–Schwarz: $\mathrm{Var}_{K|x}\varphi_{x,s}\ge\frac12\mathbb E_{K|x}\varphi_{x,s}^2$ for a non-majority label
-- statement:
--   Let the sampling scheme be as in the model, $F$ local functions into a finite alphabet, $g$ a coordinatewise majority of $F$ and $a>0$. Let $x$ be an element of positive marginal mass and $s\ne g(x)$, and write $\mathbb E_{K|x}$, $P_{K|x}$ for $K\sim\mu(\cdot\mid x\in K)$. Then $P_{K|x}[F_K(x)=s]\le\frac12$,
--   $$\big(\mathbb E_{K|x}\varphi_{x,s}\big)^2\le P_{K|x}[F_K(x)=s]\;\mathbb E_{K|x}\varphi_{x,s}^2\le\frac12\,\mathbb E_{K|x}\varphi_{x,s}^2,$$
--   and consequently
--   $$\mathrm{Var}_{K|x}\varphi_{x,s}\ge\frac12\,\mathbb E_{K|x}\varphi_{x,s}^2 .$$
--
--   This is the variance lower bound that lets the spectral gap of $M_x$ control the second moment of $\varphi_{x,s}$ in eq. (3).
--
--   Differences from the source:
--   - generalization: conditions on the downward kernel and hypotheses 1–2 stated for each top set K → required only for top sets K with μ(K) > 0; reason: §1.1 (p.4) states them for every K of positive mass and §2 (p.7) omits faces of zero mass; the Lean hypotheses are implied by the printed ones
--   - encoding: local functions F_K : K → Σ → F : Finset V → V → α, with every comparison restricted to x ∈ K (resp. x ∈ H); reason: values F K x with x ∉ K never enter any statement; same instances
--   - encoding: probabilities and expectations under μ, D(·|K), U(·|H), μ(·|x ∈ K) → finite weighted sums; U(K|H) = μ(K)D(H|K)/μ_H(H) and μ_x(K) = μ(K)1[x∈K]/P[x∈K] with the convention t/0 = 0; reason: the model is finite; the convention only affects terms of zero weight
--   - encoding: Var_{K|x} φ → ∑ μ_x φ² − (∑ μ_x φ)²; reason: the variance of φ under the probability vector μ_x (x of positive mass)
--   - generalization: a step of the proof of Theorem 7, under all hypotheses of Theorem 7 → only the standing model (no hypothesis 1–3) and a coordinatewise majority g; reason: the step uses only these hypotheses; the Lean statement specializes to the source's setting
-- source:
--   Tali Kaufman, Huy Tuan Pham, Exact Agreement Expansion up to the Top via Non-polarity, STOC 2027 submission #736 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/736.pdf (source.pdf sha256 04ba433ef4a669f9160de90c29bfff3152be2a1d08e50186f52e514c298f5d49), p.10, Section 3.1, proof of Theorem 7 (Cauchy–Schwarz display and 'Consequently Var_{K|x} φ_{x,s} ≥ ½ E_{K|x} φ²_{x,s}')

import Mathlib
import Definitions.Def_AgreementTop736_Exact_Regularized

namespace AgreementTop736.Exact

open Finset Scheme

/-- §3.1, p.10 (proof of Theorem 7): for an element `x` of positive marginal mass, a label
`s ≠ g(x)` with `g` a coordinatewise majority, and `a > 0`,
`P_{K|x}[F_K(x) = s] ≤ 1/2`, `(E_{K|x} φ_{x,s})² ≤ P_{K|x}[F_K(x) = s] E_{K|x} φ²_{x,s} ≤ ½ E_{K|x} φ²_{x,s}`,
and consequently `Var_{K|x} φ_{x,s} ≥ ½ E_{K|x} φ²_{x,s}`. -/
theorem sec3_1_cauchy_schwarz_variance {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Fintype α] [DecidableEq α]
    (S : Scheme V) (hS : S.IsValid) (F : Finset V → V → α) (g : V → α)
    (hg : S.IsCoordMajority F g) {a : ℝ} (ha : 0 < a) (x : V) (hx : 0 < S.pointMass x)
    (s : α) (hs : s ≠ g x) :
    S.labelFreq F x s ≤ 1 / 2 ∧
    (∑ K, S.μx x K * phi F g a x s K) ^ 2 ≤
      S.labelFreq F x s * ∑ K, S.μx x K * phi F g a x s K ^ 2 ∧
    S.labelFreq F x s * ∑ K, S.μx x K * phi F g a x s K ^ 2 ≤
      (1 / 2) * ∑ K, S.μx x K * phi F g a x s K ^ 2 ∧
    (1 / 2) * ∑ K, S.μx x K * phi F g a x s K ^ 2 ≤
      variance (S.μx x) (phi F g a x s) := by sorry

end AgreementTop736.Exact
