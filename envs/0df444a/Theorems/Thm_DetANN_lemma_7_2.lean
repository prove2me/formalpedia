-- Prove2me | Theorems.Thm_DetANN_lemma_7_2
-- name    : DetANN.lemma_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:26:42.947478+00:00
-- url     : https://prove2.me/theorems/63c40975-35a6-48e9-8bf7-37c2f542fe29
-- title:
--   Lemma 7.2, p.17 — $\mathbb E_I\|a_I-a\|^2\le\frac{\rho^2}{1-\rho^2}\mathcal V$ for expander walks, $\rho=\theta_0^\ell$
-- statement:
--   Let $G$ be an undirected $\Delta$-regular multigraph on $[d]$ ($\Delta\ge1$) whose normalized adjacency matrix $W$ satisfies $\|Wf\|_2\le\theta_0\|f\|_2$ for every $f\in\mathbb R^d$ with $\sum_vf(v)=0$, where $0\le\theta_0<1$. Fix an integer $\ell\ge1$ and let $S_v$ be the tuple of endpoints of all $\Delta^\ell$ walks of length $\ell$ from $v$. Choose $V$ uniformly in $[d]$ and a uniform occurrence $I$ from $S_V$. For vectors $x_1,\dots,x_d,x^\star\in\mathbb R^d$ let $a_i=\mathbb E[x_V-x^\star\mid I=i]$, $a=\mathbb E[x_V-x^\star]$ and $\mathcal V=\mathbb E\|x_V-x^\star-a_I\|_2^2$. With $\rho=\theta_0^\ell<1$,
--
--   $$\mathbb E_I\|a_I-a\|_2^2\le\frac{\rho^2}{1-\rho^2}\,\mathcal V .$$
--
--   It replaces Lemma 5.1: observing one block changes the expected location of the returned point only by an amount controlled by the expansion of $G$.
--
--   Differences from the source:
--   - generalization: the answers x_v ∈ P of the local structures and a nearest neighbor x⋆ → arbitrary vectors x_v, x⋆ ∈ ℝ^d; reason: the argument uses no property of these vectors
--   - generalization: the graph of Lemma 7.1 (Δ ≥ 2, θ₀ ∈ (0, 1)) → any undirected Δ-regular multigraph on [d] with Δ ≥ 1 whose W contracts mean-zero vectors by some θ₀ ∈ [0, 1); reason: the graph of Lemma 7.1 is such a graph
--   - encoding: expectations over V and a uniform occurrence; ‖Wf‖₂ ≤ θ₀‖f‖₂ → finite uniform averages over [d] × walks; Σ_u (Wf)_u² ≤ θ₀² Σ_v f_v²; reason: the averages are the expectations; the squared bound is equivalent for θ₀ ≥ 0
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), Lemma 7.2, p.17 (PDF p.17)

import Mathlib
import Definitions.Def_DetANN_Multigraph
import Definitions.Def_DetANN_TupleFamily

namespace DetANN

/-- **Lemma 7.2** (Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High Dimensions*, STOC 2027
submission (manuscript sha256 96f0ad57…), p.17).
Let `W` be the normalized adjacency matrix of an undirected `Δ`-regular multigraph on `[d]` with
`‖W f‖ ≤ θ₀‖f‖` for every mean-zero `f`, `0 ≤ θ₀ < 1`, and let `ℓ ≥ 1`. For the walk family (tuple of
`v` = endpoints of all length-`ℓ` walks from `v`) and `ρ = θ₀^ℓ < 1`:
`E_I ‖a_I − a‖² ≤ ρ²/(1 − ρ²) · 𝒱`.

**Formalization Note.** The walk family is `S = walkEnd nbr ℓ : [d] → (Fin ℓ → Fin Δ) → [d]`;
expectations are finite averages as in `DetANN.TupleFamily`. The answers `x_v` and the point `x⋆` are
arbitrary vectors of `ℝ^d` (the argument uses no property of them), and `θ₀ = 0` and any `Δ ≥ 1`
are allowed (the paper: `θ₀ ∈ (0, 1)`, `Δ ≥ 2`). The spectral hypothesis is stated squared
(`DetANN.ContractsMeanZero`). -/
theorem lemma_7_2 {d Δ : ℕ} (nbr : Fin d → Fin Δ → Fin d) (hΔ : 1 ≤ Δ)
    (hund : IsUndirected nbr) (θ₀ : ℝ) (hθ0 : 0 ≤ θ₀) (hθ1 : θ₀ < 1)
    (hW : ContractsMeanZero (adjMatrix nbr) θ₀) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (x : Fin d → EuclideanSpace ℝ (Fin d)) (xs : EuclideanSpace ℝ (Fin d)) :
    betweenVar (walkEnd nbr ℓ) x xs ≤
      (θ₀ ^ ℓ) ^ 2 / (1 - (θ₀ ^ ℓ) ^ 2) * withinVar (walkEnd nbr ℓ) x xs := by sorry

end DetANN
