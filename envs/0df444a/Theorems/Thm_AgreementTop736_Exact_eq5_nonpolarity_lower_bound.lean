-- Prove2me | Theorems.Thm_AgreementTop736_Exact_eq5_nonpolarity_lower_bound
-- name    : AgreementTop736.Exact.eq5_nonpolarity_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:19.409441+00:00
-- url     : https://prove2.me/theorems/ee648477-39d4-46cd-8422-455256671d19
-- title:
--   Section 3.1, eq. (5) — $E\ge\rho\gamma V$
-- statement:
--   Let the sampling scheme satisfy hypotheses 1 and 3 of Theorem 7 with $\gamma>0$, let $F$ be local functions into a finite alphabet, $g$ a coordinatewise majority and $a>0$. Then the weighted non-polarity of eq. (4) and the regularized disagreement satisfy
--   $$E\ \ge\ \rho\gamma V .$$
--
--   This is the spectral half of the proof: the gap of the element-conditioned walks forces the non-polarity to be at least proportional to the regularized distance from the majority.
--
--   Differences from the source:
--   - generalization: conditions on the downward kernel and hypotheses 1–2 stated for each top set K → required only for top sets K with μ(K) > 0; reason: §1.1 (p.4) states them for every K of positive mass and §2 (p.7) omits faces of zero mass; the Lean hypotheses are implied by the printed ones
--   - encoding: local functions F_K : K → Σ → F : Finset V → V → α, with every comparison restricted to x ∈ K (resp. x ∈ H); reason: values F K x with x ∉ K never enter any statement; same instances
--   - encoding: probabilities and expectations under μ, D(·|K), U(·|H), μ(·|x ∈ K) → finite weighted sums; U(K|H) = μ(K)D(H|K)/μ_H(H) and μ_x(K) = μ(K)1[x∈K]/P[x∈K] with the convention t/0 = 0; reason: the model is finite; the convention only affects terms of zero weight
--   - encoding: M_x has spectral gap γ_x = 1 − λ₂(M_x) ≥ γ → Poincaré inequality γ Var_{μ_x}(f) ≤ ½ E_{K∼μ_x, K'∼M_x(K,·)}(f(K) − f(K'))² for every real f on top sets; reason: the paper's own displayed form of the gap (§1.1, p.4); equivalent for the reversible M_x (reversible under hypothesis 1, p.8), and the proof uses only this form
--   - encoding: H sampled from D(·|K) conditioned on x ∈ H → weight D(H|K)1[x∈H]/P_{H∼D(·|K)}[x∈H]; reason: the definition of conditioning; under hypothesis 1 the denominator is ρ > 0 for every K ∋ x of positive mass
--   - generalization: a step of the proof of Theorem 7, under all hypotheses of Theorem 7 → the standing model, hypotheses 1 and 3, and a coordinatewise majority g (no hypothesis 2); reason: the step uses only these hypotheses; the Lean statement specializes to the source's setting
-- source:
--   Tali Kaufman, Huy Tuan Pham, Exact Agreement Expansion up to the Top via Non-polarity, STOC 2027 submission #736 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/736.pdf (source.pdf sha256 04ba433ef4a669f9160de90c29bfff3152be2a1d08e50186f52e514c298f5d49), p.10, Section 3.1, eq. (5)

import Mathlib
import Definitions.Def_AgreementTop736_Exact_Regularized

namespace AgreementTop736.Exact

open Finset Scheme

/-- §3.1, eq. (5), p.10: under hypotheses 1 and 3 of Theorem 7, for a coordinatewise majority `g`
and `a > 0`, the weighted non-polarity satisfies `E ≥ ρ γ V`. -/
theorem eq5_nonpolarity_lower_bound {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Fintype α] [DecidableEq α]
    (S : Scheme V) (hS : S.IsValid) (h1 : S.UniformInclusion) {γ : ℝ} (hγ : 0 < γ)
    (h3 : S.HasConditionedGap γ) (F : Finset V → V → α) (g : V → α)
    (hg : S.IsCoordMajority F g) {a : ℝ} (ha : 0 < a) :
    S.ρ * γ * S.Vreg F g a ≤ S.Enp F g a := by sorry

end AgreementTop736.Exact
