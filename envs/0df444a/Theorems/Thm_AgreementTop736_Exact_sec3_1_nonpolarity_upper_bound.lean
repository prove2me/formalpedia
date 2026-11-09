-- Prove2me | Theorems.Thm_AgreementTop736_Exact_sec3_1_nonpolarity_upper_bound
-- name    : AgreementTop736.Exact.sec3_1_nonpolarity_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:23.811753+00:00
-- url     : https://prove2.me/theorems/c4cd2eb9-086e-42ce-9e99-f4e2864a872d
-- title:
--   Section 3.1, p.11 — $E\le\frac{4(1-\rho)}{a}V+4\rho\tau$
-- statement:
--   Let the sampling scheme satisfy hypothesis 2 of Theorem 7, let $F$ be local functions into a finite alphabet with rejection probability $\tau$, $g:V\to\Sigma$ any function and $a>0$. Then the weighted non-polarity of eq. (4) satisfies
--   $$E\ \le\ \frac{4(1-\rho)}{a}\,V+4\rho\tau .$$
--
--   Together with (5) this sandwiches $E$ between $\rho\gamma V$ and a multiple of $\tau$ plus a small multiple of $V$, which yields Theorem 7 for a suitable choice of $a$.
--
--   Differences from the source:
--   - generalization: conditions on the downward kernel and hypotheses 1–2 stated for each top set K → required only for top sets K with μ(K) > 0; reason: §1.1 (p.4) states them for every K of positive mass and §2 (p.7) omits faces of zero mass; the Lean hypotheses are implied by the printed ones
--   - encoding: local functions F_K : K → Σ → F : Finset V → V → α, with every comparison restricted to x ∈ K (resp. x ∈ H); reason: values F K x with x ∉ K never enter any statement; same instances
--   - encoding: probabilities and expectations under μ, D(·|K), U(·|H), μ(·|x ∈ K) → finite weighted sums; U(K|H) = μ(K)D(H|K)/μ_H(H) and μ_x(K) = μ(K)1[x∈K]/P[x∈K] with the convention t/0 = 0; reason: the model is finite; the convention only affects terms of zero weight
--   - encoding: Var(Z | K) → ∑_H D(H|K)(Z(H) − E[Z|K])²; reason: the definition of the conditional variance under D(·|K) for K of positive mass, where D(·|K) is a probability vector
--   - generalization: a step of the proof of Theorem 7, under all hypotheses of Theorem 7 with g the coordinatewise majority → the standing model and hypothesis 2 (no hypotheses 1 and 3), and every g : V → Σ; reason: the step uses only these hypotheses; the Lean statement specializes to the source's setting
-- source:
--   Tali Kaufman, Huy Tuan Pham, Exact Agreement Expansion up to the Top via Non-polarity, STOC 2027 submission #736 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/736.pdf (source.pdf sha256 04ba433ef4a669f9160de90c29bfff3152be2a1d08e50186f52e514c298f5d49), p.11, Section 3.1, display 'Hence, E = … ≤ 4(1−ρ)/a V + 4ρτ, by using (6), and (7)'

import Mathlib
import Definitions.Def_AgreementTop736_Exact_Regularized

namespace AgreementTop736.Exact

open Finset Scheme

/-- §3.1, p.11, display following (7): under hypothesis 2 of Theorem 7, for every `g : V → α` and
`a > 0`, `E ≤ (4(1 − ρ)/a) V + 4 ρ τ`. -/
theorem sec3_1_nonpolarity_upper_bound {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Fintype α] [DecidableEq α]
    (S : Scheme V) (hS : S.IsValid) (h2 : S.VarianceBound) (F : Finset V → V → α) (g : V → α)
    {a : ℝ} (ha : 0 < a) :
    S.Enp F g a ≤ 4 * (1 - S.ρ) / a * S.Vreg F g a + 4 * S.ρ * S.rejectionProb F := by sorry

end AgreementTop736.Exact
