-- Prove2me | Theorems.Thm_AgreementTop736_Exact_exact_agreement_soundness
-- name    : AgreementTop736.Exact.exact_agreement_soundness
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:11.676502+00:00
-- url     : https://prove2.me/theorems/7b3cd409-3657-4d6d-8762-a8d6fa64f584
-- title:
--   Theorem 7 — exact agreement soundness $8/\gamma+64(1-\rho)/(\rho\gamma^2)$ from spectral gaps of element-conditioned down-up walks
-- statement:
--   Let $\mu$ be a distribution on $N$-element subsets $K$ of a finite set $V$, and let a downward kernel $D(H\mid K)$ sample $n$-element sets $H\subseteq K$, with $0<n<N$ and $\rho=n/N$. Let $U(K\mid H)$ sample $K$ conditional on $H$. Assume:
--
--   1. for each top set $K$ and every $x\in K$, $P_{H\sim D(\cdot\mid K)}[x\in H]=\rho$;
--   2. for every top set $K$ and $E\subseteq K$, with $m=|E|$ and $Z=|E\cap H|$, $\mathbb E[Z\mid K]=\rho m$ and $\mathrm{Var}(Z\mid K)\le\rho(1-\rho)m$;
--   3. for every element $x$ of positive marginal mass, the walk $M_x$ on top sets containing $x$ (sample $H$ downward conditioned on $x\in H$, then $K'$ upward from $H$) has spectral gap at least $\gamma>0$, with stationary measure $\mu(\cdot\mid x\in K)$.
--
--   Let $\Sigma$ be a finite alphabet, $F_K:K\to\Sigma$ local functions, and
--   $$\tau=P_{H,K,K'}\big[F_K|_H\ne F_{K'}|_H\big],$$
--   where $H$ has its induced marginal and $K,K'$ are independent samples conditional on $H$. Then a coordinatewise majority $g:V\to\Sigma$ exists, and every coordinatewise majority $g$ (ties broken arbitrarily) satisfies
--   $$P_K\big[F_K\ne g|_K\big]\ \le\ \Big(\frac8\gamma+\frac{64(1-\rho)}{\rho\gamma^2}\Big)\tau .$$
--
--   This is the main theorem of the paper (Theorem 1 is its informal version): exact agreement soundness on the top layer from one-sided (link) spectral expansion, with a constant independent of the alphabet and of $|V|$.
--
--   Differences from the source:
--   - generalization: conditions on the downward kernel and hypotheses 1–2 stated for each top set K → required only for top sets K with μ(K) > 0; reason: §1.1 (p.4) states them for every K of positive mass and §2 (p.7) omits faces of zero mass; the Lean hypotheses are implied by the printed ones
--   - encoding: local functions F_K : K → Σ → F : Finset V → V → α, with every comparison restricted to x ∈ K (resp. x ∈ H); reason: values F K x with x ∉ K never enter any statement; same instances
--   - encoding: probabilities and expectations under μ, D(·|K), U(·|H), μ(·|x ∈ K) → finite weighted sums; U(K|H) = μ(K)D(H|K)/μ_H(H) and μ_x(K) = μ(K)1[x∈K]/P[x∈K] with the convention t/0 = 0; reason: the model is finite; the convention only affects terms of zero weight
--   - encoding: M_x has spectral gap γ_x = 1 − λ₂(M_x) ≥ γ → Poincaré inequality γ Var_{μ_x}(f) ≤ ½ E_{K∼μ_x, K'∼M_x(K,·)}(f(K) − f(K'))² for every real f on top sets; reason: the paper's own displayed form of the gap (§1.1, p.4); equivalent for the reversible M_x (reversible under hypothesis 1, p.8), and the proof uses only this form
--   - encoding: H sampled from D(·|K) conditioned on x ∈ H → weight D(H|K)1[x∈H]/P_{H∼D(·|K)}[x∈H]; reason: the definition of conditioning; under hypothesis 1 the denominator is ρ > 0 for every K ∋ x of positive mass
--   - encoding: Var(Z | K) → ∑_H D(H|K)(Z(H) − E[Z|K])²; reason: the definition of the conditional variance under D(·|K) for K of positive mass, where D(·|K) is a probability vector
--   - encoding: coordinatewise majority: g(x) a most frequent value of F_K(x) under μ(·|x ∈ K), for every x → the maximality condition imposed at every x of positive marginal mass; reason: μ(·|x ∈ K) is undefined at elements of zero mass, and such elements lie in no top set of positive mass, so g's values there never enter the conclusion
--   - generalization: the coordinatewise majority function g satisfies (2) → a coordinatewise majority exists, and every coordinatewise majority satisfies (2); reason: the existence clause makes the statement non-vacuous and is implicit in the source; the ∀ clause is 'breaking ties arbitrarily' (p.9)
-- source:
--   Tali Kaufman, Huy Tuan Pham, Exact Agreement Expansion up to the Top via Non-polarity, STOC 2027 submission #736 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/736.pdf (source.pdf sha256 04ba433ef4a669f9160de90c29bfff3152be2a1d08e50186f52e514c298f5d49), p.9, Theorem 7, display (2) (informal version: p.4, Theorem 1)

import Mathlib
import Definitions.Def_AgreementTop736_Exact_Model

namespace AgreementTop736.Exact

open Finset Scheme

/-- Theorem 7, p.9: under the sampling conditions 1–2 and a spectral gap at least `γ > 0` of every
element-conditioned down-up walk, for every finite alphabet `α` and every family of local functions
`F`, a coordinatewise majority `g` exists, and every coordinatewise majority satisfies
`P_K[F_K ≠ g|_K] ≤ (8/γ + 64(1 − ρ)/(ργ²)) τ`. -/
theorem exact_agreement_soundness {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Fintype α] [DecidableEq α]
    (S : Scheme V) (hS : S.IsValid) (h1 : S.UniformInclusion) (h2 : S.VarianceBound)
    {γ : ℝ} (hγ : 0 < γ) (h3 : S.HasConditionedGap γ) (F : Finset V → V → α) :
    (∃ g : V → α, S.IsCoordMajority F g) ∧
    ∀ g : V → α, S.IsCoordMajority F g →
      S.disagreementProb F g ≤ (8 / γ + 64 * (1 - S.ρ) / (S.ρ * γ ^ 2)) * S.rejectionProb F := by sorry

end AgreementTop736.Exact
