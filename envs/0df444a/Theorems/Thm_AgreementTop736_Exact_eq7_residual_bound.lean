-- Prove2me | Theorems.Thm_AgreementTop736_Exact_eq7_residual_bound
-- name    : AgreementTop736.Exact.eq7_residual_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:35.159936+00:00
-- url     : https://prove2.me/theorems/2ec22d6a-781b-4eb5-9adc-ae95c8ed40fc
-- title:
--   Section 3.1, eq. (7) — $\mathbb E_{K,H}\|R(K,H)\|_2^2\le\frac{1-\rho}{a}V$
-- statement:
--   Let the sampling scheme satisfy hypothesis 2 of Theorem 7 (display (1)), let $F$ be local functions into a finite alphabet, $g:V\to\Sigma$ any function and $a>0$. Then, with $K\sim\mu$ and $H\sim D(\cdot\mid K)$,
--   $$\mathbb E_{K,H}\big\|R(K,H)\big\|_2^2\ \le\ \frac{1-\rho}{a}\,V .$$
--
--   This shows that the local witness vectors $\psi(K,H)$ are close to the restrictions $\varphi(K)|_H$, with an error controlled by the regularized disagreement.
--
--   Differences from the source:
--   - generalization: conditions on the downward kernel and hypotheses 1–2 stated for each top set K → required only for top sets K with μ(K) > 0; reason: §1.1 (p.4) states them for every K of positive mass and §2 (p.7) omits faces of zero mass; the Lean hypotheses are implied by the printed ones
--   - encoding: local functions F_K : K → Σ → F : Finset V → V → α, with every comparison restricted to x ∈ K (resp. x ∈ H); reason: values F K x with x ∉ K never enter any statement; same instances
--   - encoding: probabilities and expectations under μ, D(·|K), U(·|H), μ(·|x ∈ K) → finite weighted sums; U(K|H) = μ(K)D(H|K)/μ_H(H) and μ_x(K) = μ(K)1[x∈K]/P[x∈K] with the convention t/0 = 0; reason: the model is finite; the convention only affects terms of zero weight
--   - encoding: Var(Z | K) → ∑_H D(H|K)(Z(H) − E[Z|K])²; reason: the definition of the conditional variance under D(·|K) for K of positive mass, where D(·|K) is a probability vector
--   - generalization: a step of the proof of Theorem 7, under all hypotheses of Theorem 7 with g the coordinatewise majority → the standing model and hypothesis 2 (no hypotheses 1 and 3), and every g : V → Σ; reason: the step uses only these hypotheses; the Lean statement specializes to the source's setting
-- source:
--   Tali Kaufman, Huy Tuan Pham, Exact Agreement Expansion up to the Top via Non-polarity, STOC 2027 submission #736 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/736.pdf (source.pdf sha256 04ba433ef4a669f9160de90c29bfff3152be2a1d08e50186f52e514c298f5d49), p.11, Section 3.1, eq. (7) (with the chain of displays preceding it)

import Mathlib
import Definitions.Def_AgreementTop736_Exact_Regularized

namespace AgreementTop736.Exact

open Finset Scheme

/-- §3.1, eq. (7), p.11: under hypothesis 2 of Theorem 7, for every `g : V → α` and `a > 0`,
`E_{K,H} ‖R(K,H)‖²₂ ≤ ((1 − ρ)/a) V`, with `K ∼ μ` and `H ∼ D(· | K)`. -/
theorem eq7_residual_bound {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Fintype α] [DecidableEq α]
    (S : Scheme V) (hS : S.IsValid) (h2 : S.VarianceBound) (F : Finset V → V → α) (g : V → α)
    {a : ℝ} (ha : 0 < a) :
    ∑ K, ∑ H, S.μ K * S.D K H * S.residualSq F g a K H ≤ (1 - S.ρ) / a * S.Vreg F g a := by sorry

end AgreementTop736.Exact
