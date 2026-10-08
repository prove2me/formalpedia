-- Prove2me | Theorems.Thm_AffinePSD_InfDiv_lemma_6_4
-- name    : AffinePSD.InfDiv.lemma_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:50.94745+00:00
-- url     : https://prove2.me/theorems/d272acf7-6d8c-4eb3-a21d-d06a08d54eac
-- title:
--   Lemma 6.4 — $P^{(1)}_{x^{(1)}}*\dots*P^{(k)}_{x^{(k)}}=P^{(0)}_x$ iff the Laplace functionals are $\rho^{(j)}(t,u)e^{-\langle\psi(t,u),x\rangle}$ with $\prod\rho^{(i)}=\rho^{(0)}$
-- statement:
--   Let $k\ge2$ and let $(P^{(i)}_x)_{x\in S_d^+}\in\mathcal P$ for $i=0,1,\dots,k$. Then
--   $$P^{(1)}_{x^{(1)}}*\dots*P^{(k)}_{x^{(k)}}=P^{(0)}_x\qquad\forall x^{(i)}\in S_d^+,\ x=x^{(1)}+\dots+x^{(k)},\qquad(6.6)$$
--   holds if and only if the following holds. For all $N\in\mathbb N_0$, $\mathbf t=(t_1,\dots,t_N)\in\mathbb R_+^N$ and $\mathbf u=(u^{(1)},\dots,u^{(N)})\in(S_d^+)^N$, there are numbers $0<\rho^{(i)}(\mathbf t,\mathbf u)\le1$ ($i=0,\dots,k$) and a matrix $\psi(\mathbf t,\mathbf u)\in S_d^+$ such that $\prod_{i=1}^k\rho^{(i)}(\mathbf t,\mathbf u)=\rho^{(0)}(\mathbf t,\mathbf u)$ and
--   $$\mathbb E^{(j)}_x\Big[e^{-\sum_{i=1}^N\langle u^{(i)},X_{t_i}\rangle}\Big]=\rho^{(j)}(\mathbf t,\mathbf u)\,e^{-\langle\psi(\mathbf t,\mathbf u),x\rangle}\qquad\forall x\in S_d^+,\ j=0,1,\dots,k.\qquad(6.7)$$
--   The expectations use the convention $f(\Delta)=0$: the integrand vanishes on paths that are at $\Delta$ at some $t_i$.
--
--   This turns the path-space identity (6.6) into an exponential-affine property of all finite-dimensional Laplace functionals. With it, infinite decomposability implies the affine property in Theorem 2.9.
--
--   **Formalization Note** $P^{(0)}$ is `P0`, and $P^{(i)}$ for $i=1,\dots,k$ is `P (i-1)`. The paper's statement allows every $k$, but its proof begins "Fix $k>1$", and for $k=1$ the lemma is false: (6.6) then holds for every family in $\mathcal P$, while (6.7) forces the affine form. So the hypothesis $k\ge2$ is the proof's. $\mathcal P$, $\Omega$ and $*$ are encoded as in the `PathSpace` definitions, with $\Delta$ absorbing for addition.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), §6.3, Lemma 6.4, (6.6)–(6.7), p. 55 (proof: "Fix k > 1")

import Mathlib
import Definitions.Def_AffinePSD_InfDiv_Cone
import Definitions.Def_AffinePSD_InfDiv_PathSpace

open MeasureTheory
open scoped NNReal

namespace AffinePSD.InfDiv

/-- Lemma 6.4 (arXiv:0910.0137v3, §6.3, p. 55). Let `(P^{(i)}_x)_{x ∈ S_d^+} ∈ 𝒫`,
`i = 0, 1, …, k`. Then
`P^{(1)}_{x^{(1)}} ∗ ⋯ ∗ P^{(k)}_{x^{(k)}} = P^{(0)}_x` for all `x^{(i)} ∈ S_d^+`,
`x = x^{(1)} + ⋯ + x^{(k)}` (6.6), if and only if for all `t ∈ ℝ_+^N`, `u ∈ (S_d^+)^N`, `N ∈ ℕ_0`,
there are `0 < ρ^{(i)}(t,u) ≤ 1` and `ψ(t,u) ∈ S_d^+` with `∏_{i=1}^k ρ^{(i)} = ρ^{(0)}` and
`E^{(j)}_x[e^{−Σ_i ⟨u^{(i)}, X_{t_i}⟩}] = ρ^{(j)}(t,u) e^{−⟨ψ(t,u), x⟩}` for all `x`, `j` (6.7).
Formalization Note: `P0` is `P^{(0)}` and `P i` is `P^{(i+1)}`; `k ≥ 2` is the proof's
"Fix `k > 1`" (for `k = 1`, (6.6) holds for every family in `𝒫` while (6.7) forces the affine
form). The expectation uses `f(Δ) = 0` (`lapPath`). `𝒫`, `Ω`, `∗` are encoded as in
`InPWith`, `Path`, `convK`. -/
theorem lemma_6_4 {d k : ℕ} (hk : 2 ≤ k) (P0 : AffinePSD.Necessity.Cone d → Measure (Path d))
    (P : Fin k → AffinePSD.Necessity.Cone d → Measure (Path d)) (h0 : InP P0) (hP : ∀ i, InP (P i)) :
    (∀ xs : Fin k → AffinePSD.Necessity.Cone d, convK k (fun i => P i (xs i)) = P0 (coneSum xs)) ↔
      ∀ (N : ℕ) (t : Fin N → ℝ≥0) (u : Fin N → AffinePSD.Necessity.Cone d),
        ∃ (ρ0 : ℝ) (ρ : Fin k → ℝ) (ψ : AffinePSD.Necessity.Cone d),
          (0 < ρ0 ∧ ρ0 ≤ 1) ∧ (∀ i, 0 < ρ i ∧ ρ i ≤ 1) ∧ ∏ i, ρ i = ρ0 ∧
          (∀ x : AffinePSD.Necessity.Cone d, ∫ ω, lapPath t u ω ∂(P0 x) = ρ0 * Real.exp (- AffinePSD.Necessity.tr ψ.1 x.1)) ∧
          ∀ (j : Fin k) (x : AffinePSD.Necessity.Cone d),
            ∫ ω, lapPath t u ω ∂(P j x) = ρ j * Real.exp (- AffinePSD.Necessity.tr ψ.1 x.1) := by sorry

end AffinePSD.InfDiv
