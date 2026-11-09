-- Prove2me | Theorems.Thm_AgreementTop736_Exact_eq6_local_witness_bound
-- name    : AgreementTop736.Exact.eq6_local_witness_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:45.955236+00:00
-- url     : https://prove2.me/theorems/cc439798-8c28-4a12-941f-2083e47f1905
-- title:
--   Section 3.1, eq. (6) — $\mathbb E_{H,K,K'}\|\psi(K,H)-\psi(K',H)\|_2^2\le2\rho\tau$
-- statement:
--   Let the sampling scheme be as in the model, $F$ local functions into a finite alphabet with rejection probability $\tau$, $g:V\to\Sigma$ any function and $a>0$. Then
--   $$\mathbb E_{H,K,K'}\big\|\psi(K,H)-\psi(K',H)\big\|_2^2\ \le\ 2\rho\tau,$$
--   where $(H,K,K')$ follows the joint law of the agreement test and the norm runs over the coordinates $(x,s)$ with $x\in H$, $s\ne g(x)$.
--
--   This bounds the local (test-face) version of the non-polarity by the rejection probability, since $\psi(K,H)$ depends only on $F_K|_H$.
--
--   Differences from the source:
--   - generalization: conditions on the downward kernel and hypotheses 1–2 stated for each top set K → required only for top sets K with μ(K) > 0; reason: §1.1 (p.4) states them for every K of positive mass and §2 (p.7) omits faces of zero mass; the Lean hypotheses are implied by the printed ones
--   - encoding: local functions F_K : K → Σ → F : Finset V → V → α, with every comparison restricted to x ∈ K (resp. x ∈ H); reason: values F K x with x ∉ K never enter any statement; same instances
--   - encoding: probabilities and expectations under μ, D(·|K), U(·|H), μ(·|x ∈ K) → finite weighted sums; U(K|H) = μ(K)D(H|K)/μ_H(H) and μ_x(K) = μ(K)1[x∈K]/P[x∈K] with the convention t/0 = 0; reason: the model is finite; the convention only affects terms of zero weight
--   - generalization: a step of the proof of Theorem 7, under all hypotheses of Theorem 7 with g the coordinatewise majority → only the standing model (no hypothesis 1–3), and every g : V → Σ; reason: the step uses only these hypotheses; the Lean statement specializes to the source's setting
-- source:
--   Tali Kaufman, Huy Tuan Pham, Exact Agreement Expansion up to the Top via Non-polarity, STOC 2027 submission #736 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/736.pdf (source.pdf sha256 04ba433ef4a669f9160de90c29bfff3152be2a1d08e50186f52e514c298f5d49), p.10, Section 3.1, eq. (6)

import Mathlib
import Definitions.Def_AgreementTop736_Exact_Regularized

namespace AgreementTop736.Exact

open Finset Scheme

/-- §3.1, eq. (6), p.10: for every `g : V → α` and `a > 0`,
`E_{H,K,K'} ‖ψ(K,H) − ψ(K',H)‖²₂ ≤ 2 ρ τ`. -/
theorem eq6_local_witness_bound {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Fintype α] [DecidableEq α]
    (S : Scheme V) (hS : S.IsValid) (F : Finset V → V → α) (g : V → α) {a : ℝ} (ha : 0 < a) :
    ∑ H, ∑ K, ∑ K', S.testWeight H K K' * S.psiDistSq F g a H K K' ≤
      2 * S.ρ * S.rejectionProb F := by sorry

end AgreementTop736.Exact
