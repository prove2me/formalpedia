-- Prove2me | Theorems.Thm_FeedbackSwitching_lemma_4
-- name    : FeedbackSwitching.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:40:41.731966+00:00
-- url     : https://prove2.me/theorems/ff359ab4-78f9-4b24-a8c2-0177e3e9534b
-- title:
--   Lemma 4 — spectral structure: $\mathrm{diag}(p)A$ symmetric, eigenvalues in $[1/2,\lambda_{\max}]$, $(I+\tau A)(2P_\tau-I)=I$
-- statement:
--   Let $p,x$ be positive probability vectors with $x\ge p/2$, $\lambda_s=x_s/p_s$, and $A=\mathrm{diag}(\lambda)-\lambda x^{\mathsf T}$, i.e. $(Af)_s=\lambda_s(f_s-x^{\mathsf T}f)$.
--
--   1. $\mathrm{diag}(p)A=\mathrm{diag}(x)-xx^{\mathsf T}$ is symmetric, $A\mathbf 1=0$, and $\langle f,Af\rangle_p=\mathrm{Var}_x(f)$ for every $f$. There are $p$-centered vectors $\phi_1,\dots,\phi_{K-1}$, orthonormal for $\langle\cdot,\cdot\rangle_p$, with $A\phi_n=\alpha_n\phi_n$ and $\tfrac12\le\alpha_n\le\lambda_{\max}=\max_s\lambda_s$; together with $\mathbf 1$ they form a basis of $\mathbb R^K$.
--   2. For every rate $0<\tau\le1$, $(I+\tau A)(2P_\tau-I)=I$. Consequently $P_\tau\mathbf 1=\mathbf 1$ and $P_\tau\phi_n=\nu_\tau(\alpha_n)\phi_n$, where $\nu_\tau(\alpha)=\frac{2+\tau\alpha}{2(1+\tau\alpha)}$.
--
--   All members of the holding family are explicit functions of one matrix $A$ and share one eigenbasis.
--
--   **Formalization Note** The eigenvectors are indexed by `Fin (K-1)`; $\alpha_n\le\lambda_{\max}$ is written as "$\alpha_n\le\lambda_s$ for some $s$"; the basis property is stated as spanning (with orthonormality and $\langle\mathbf 1,\phi_n\rangle_p=0$ this is a basis). The vectors $\phi_n$ are chosen once, independently of $\tau$.
--
--   Differences from the source:
--   - encoding: 1/2 ≤ α_n ≤ λ_max; together with 1 they form a basis of ℝ^K → 1/2 ≤ α_n and α_n ≤ λ_s for some s; every f is c·1 + Σ_n a_n φ_n; reason: λ_max is the maximum over the finite set of actions; K vectors that span ℝ^K and are orthonormal for ⟨·,·⟩_p form a basis; same instances
--   - generalization: 0 < τ ≤ 1 fixed at the start of the lemma, with φ_n, α_n chosen for it → one family (φ_n, α_n) chosen before τ, with (ii) for every τ ∈ (0, 1]; reason: the φ_n come from A, which does not depend on τ, and p.17 and p.27 say the chains share one eigenbasis; fixing τ gives the printed statement
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Lemma 4, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_FeedbackSwitching_holdingP
open Matrix

namespace FeedbackSwitching

/-- **Lemma 4 (Spectral structure)**, p.27 (PDF p.29). Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, *The Price of Partial Information with
Switching Costs: A Complete Characterization for Feedback Graphs*, arXiv:2606.03851 (held version,
sha256 ded8f8bc…).

Let `(p, x)` be as in Definition 2, `0 < τ ≤ 1`, and `A = diag(λ) − λxᵀ`, i.e.
`(Af)_s = λ_s(f_s − xᵀf)` (Eq. (33)).
(i) `diag(p)A = diag(x) − xxᵀ` is symmetric, `A1 = 0`, and `⟨f, Af⟩_p = Var_x(f)` for every `f`.
There are `p`-centered vectors `φ_1, …, φ_{K−1}`, orthonormal for `⟨·,·⟩_p`, with `Aφ_n = α_n φ_n`
and `1/2 ≤ α_n ≤ λ_max`. Together with `1` they form a basis of `ℝ^K`.
(ii) `(I + τA)(2P_τ − I) = I`. Consequently `P_τ1 = 1` and `P_τφ_n = ν_τ(α_n)φ_n` for every `n`,
where `ν_τ(α) = (2 + τα)/(2(1 + τα))`.

**Formalization Note.** The eigenvectors are indexed by `Fin (K − 1)` (`K ≥ 1` since `p` is a
probability vector). `α_n ≤ λ_max = max_s λ_s` is written `∃ s, α_n ≤ λ_s`. "Together with `1`
they form a basis" is written as spanning; with orthonormality for `⟨·,·⟩_p` (and `⟨1, φ_n⟩_p = 0`,
`⟨1, 1⟩_p = 1`) the `K` vectors are independent. The rate `τ` is quantified inside: one family
`(φ_n, α_n)`, built from `A` alone, serves every `τ ∈ (0, 1]` (p.27: "every member is a function of
one matrix that does not depend on the rate"; p.17: "The chains of Section 4.2 share one
eigenbasis"). -/
theorem lemma_4 {K : ℕ} (p x : Fin K → ℝ) (hpx : IsHoldingPair p x) :
    diagonal p * Amat p x = diagonal x - vecMulVec x x ∧
    (diagonal p * Amat p x).IsSymm ∧
    Amat p x *ᵥ (fun _ => (1 : ℝ)) = 0 ∧
    (∀ f : Fin K → ℝ, wInner p f (Amat p x *ᵥ f) = wVar x f) ∧
    (∃ (φ : Fin (K - 1) → Fin K → ℝ) (α : Fin (K - 1) → ℝ),
      (∀ n, ∑ i, p i * φ n i = 0) ∧
      (∀ n n', wInner p (φ n) (φ n') = if n = n' then 1 else 0) ∧
      (∀ n, Amat p x *ᵥ φ n = α n • φ n) ∧
      (∀ n, 1 / 2 ≤ α n ∧ ∃ s, α n ≤ lam p x s) ∧
      (∀ f : Fin K → ℝ, ∃ (c : ℝ) (a : Fin (K - 1) → ℝ),
        f = c • (fun _ => (1 : ℝ)) + ∑ n, a n • φ n) ∧
      (∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ n, holdingP p x τ *ᵥ φ n = nuRate τ (α n) • φ n)) ∧
    ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      (1 + τ • Amat p x) * (2 • holdingP p x τ - 1) = 1 ∧
      holdingP p x τ *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1 := by sorry

end FeedbackSwitching
