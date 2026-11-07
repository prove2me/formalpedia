-- Prove2me | Theorems.Thm_BetheKS_theorem_2_2
-- name    : BetheKS.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:25.604452+00:00
-- url     : https://prove2.me/theorems/34dee599-8c6e-45c7-9c94-9ef175fb889a
-- title:
--   Theorem 2.2 — outlier eigenvalues and eigenspaces of $H(\pm\sqrt d,G_n)$
-- statement:
--   Let $G_n\sim\mathrm{SBM}_n(P,\pi)$ have fixed parameters and common expected degree $d>1$. List the informative planted eigenvalues, counted with multiplicity, as $\mu^+_1\ge\dots\ge\mu^+_{r_+}>\sqrt d$ and $\mu^-_1\le\dots\le\mu^-_{r_-}<-\sqrt d$, and order the eigenvalues of each Bethe Hessian increasingly. Then:
--
--   1. there is a deterministic strictly increasing function $\delta:(\sqrt d,d]\to(0,\infty)$ such that, as $n\to\infty$,
--   $$
--   \lambda_i(H(\sqrt d,G_n))\xrightarrow{\mathbb P}-\delta(\mu^+_i)\quad(i\in[r_+]),\qquad \lambda_j(H(-\sqrt d,G_n))\xrightarrow{\mathbb P}-\delta(|\mu^-_j|)\quad(j\in[r_-]);
--   $$
--   2. for each distinct informative eigenvalue $\mu$, with $E_{\mu,n}$ the span of the corresponding outlier eigenvectors, there is $c_\mu>0$, depending only on $Q$ and $\mu$, such that with probability tending to one
--   $$
--   \|\operatorname{Proj}_{E_{\mu,n}}x\|_2\ge c_\mu\|x\|_2\qquad\text{for every }x\in\operatorname{span}\{X_i:\mu_i=\mu\};
--   $$
--   3. if $\mu_i$ is simple and $v_{i,n}$ is its unit outlier eigenvector, there is a deterministic $q_{\mu_i}>0$ with
--   $$
--   \frac{|\langle v_{i,n},X_i\rangle|}{\sqrt n}=q_{\mu_i}+o_{\mathbb P}(1).\qquad(2.3)
--   $$
--
--   This identifies the informative Bethe-Hessian eigenspaces throughout the fixed-degree regime $d>1$; Theorem 2.3 rounds them.
--
--   **Formalization Note** Indices are 0-based. In (3), $X_i=\phi\circ\sigma$ for any $\phi$ with $Q\phi=\mu_i\phi$ and $\sum_a\pi_a\phi(a)^2=1$ (both signs).
--
--   Differences from the source:
--
--   - encoding: eigenvalues of Q counted with multiplicity → real roots of the characteristic polynomial of Q, with multiplicity; reason: Q is diagonalizable with real spectrum, so algebraic and geometric multiplicities agree
--   - encoding: n → ∞ with |σ⁻¹(i)| = π_i n → n → ∞ along 𝒩_π = {n : π_i n ∈ ℕ ∀ i}, for every sequence of exact-size label maps σ_n; reason: the paper's deterministic community-size convention (p.4); the statement is uniform over the labelings
--   - encoding: π a distribution on [r] → every π_a > 0; reason: the r eigenfunctions orthonormal in L²(π) that the paper uses exist only then; excludes undefined cases
--   - encoding: edge probability P_{σ(u)σ(v)}/n → min(1, P_{σ(u)σ(v)}/n); reason: affects only finitely many n, not the limits
--   - reading: the outlier eigenvectors of H(±√d, G_n) → every choice of increasing orthonormal eigenbases of H(±√d, G), fixed for each graph before the probability; reason: the eigenvectors are unique only up to rotations within repeated eigenvalues; the universal reading is the stronger one
--   - reading: c_μ > 0, depending only on Q and μ → one function c(Q, μ), chosen before the parameters (P, π), with c(Q, μ) > 0 and the projection property; reason: the literal meaning of 'depending only on Q and μ'
--   - encoding: |⟨v_{i,n}, X_i⟩|/√n = q + o_P(1) → convergence in probability to q, for every normalized eigenfunction ϕ_i and every choice of eigenbasis; reason: o_P(1) is convergence in probability; X_i is determined up to sign by the normalization
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), Theorem 2.2, pp.4–5 (PDF pp.5–6), (2.3)

import Mathlib
import Definitions.Def_BetheKS_HasProjProperty

set_option autoImplicit false

namespace BetheKS

/-- **Theorem 2.2 (Outlier eigenvalues and eigenspaces)** — Dong, McKenzie, arXiv:2610.41802 (held
version, sha256 4da41e16…), pp.4–5 (PDF pp.5–6). For `Gₙ ∼ SBMₙ(P, π)` with fixed parameters and
common expected degree `d > 1`:
1. there is a deterministic strictly increasing `δ : (√d, d] → (0, ∞)` with
   `λᵢ(H(√d, Gₙ)) →ᴾ −δ(µᵢ⁺)` (`i ∈ [r₊]`) and `λⱼ(H(−√d, Gₙ)) →ᴾ −δ(|µⱼ⁻|)` (`j ∈ [r₋]`),
   eigenvalues ordered from most negative to most positive;
2. there are constants `c_µ > 0`, depending only on `Q` and `µ`, with
   `‖Proj_{E_{µ,n}} x‖₂ ≥ c_µ ‖x‖₂` for every `x ∈ span{Xᵢ : µᵢ = µ}`, with probability tending to one;
3. if `µᵢ` is simple and `vᵢ,ₙ` is its unit outlier eigenvector, there is a deterministic `q_{µᵢ} > 0`
   with `|⟨vᵢ,ₙ, Xᵢ⟩|/√n = q_{µᵢ} + o_P(1)` (2.3).

**Formalization Note.** Indices are 0-based. `c` is one function of `(Q, µ)`, chosen before the
parameters. Limits run over `n ∈ 𝒩_π` for every exact-size labeling sequence, and over every choice
of increasing orthonormal eigenbases. In (3), `Xᵢ = ϕᵢ ∘ σ` with `Q ϕᵢ = µᵢ ϕᵢ` and `∑ₐ πₐ ϕᵢ(a)² = 1`
(the paper's normalization); `ϕᵢ` is determined up to sign, and both signs are covered. -/
theorem theorem_2_2 (r : ℕ) :
    (∀ p : SBMParams r, ∃ δf : ℝ → ℝ,
      StrictMonoOn δf (Set.Ioc (Real.sqrt p.d) p.d) ∧
      (∀ x ∈ Set.Ioc (Real.sqrt p.d) p.d, 0 < δf x) ∧
      ∀ σs : ∀ n : ℕ, Fin n → Fin r, IsExactSeq p σs →
        (∀ i : ℕ, i < rplus p →
          ConvInProb p σs (fun _ G => eigInc (bh (Real.sqrt p.d) G) i)
            (-δf ((posInf p).getD i 0))) ∧
        (∀ j : ℕ, j < rminus p →
          ConvInProb p σs (fun _ G => eigInc (bh (-Real.sqrt p.d) G) j)
            (-δf |(negInf p).getD j 0|))) ∧
    (∃ c : Matrix (Fin r) (Fin r) ℝ → ℝ → ℝ, ∀ p : SBMParams r, HasProjProperty p (c (signal p))) ∧
    (∀ p : SBMParams r, ∀ μ ∈ (informative p).toFinset, Multiset.count μ (qRoots p) = 1 →
      ∃ q : ℝ, 0 < q ∧
        ∀ ϕ : Fin r → ℝ, (signal p).mulVec ϕ = μ • ϕ → ∑ a, p.pi a * ϕ a ^ 2 = 1 →
        ∀ σs : ∀ n : ℕ, Fin n → Fin r, IsExactSeq p σs →
        ∀ Bp : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), IncEigenbasis (bh (Real.sqrt p.d) G),
        ∀ Bm : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), IncEigenbasis (bh (-Real.sqrt p.d) G),
          ConvInProb p σs
            (fun n G => |inner ℝ (outlierVec p (Bp n G) (Bm n G) μ) (WithLp.toLp 2 (ϕ ∘ σs n))| /
              Real.sqrt n) q) := by sorry

end BetheKS
