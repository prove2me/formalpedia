-- Prove2me | Theorems.Thm_FermiGaussMix_theorem_A_1
-- name    : FermiGaussMix.theorem_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:02:00.430866+00:00
-- url     : https://prove2.me/theorems/9eedd1c4-cd94-4537-9d12-6bdd3e64093b
-- title:
--   Theorem A.1 — for $g\le g_{\rm mix}$ the Gibbs state of a local $H=H_0+V$ lies in $\operatorname{conv}(G_n)$
-- statement:
--   Consider $n$ fermionic modes and a Hamiltonian $H=H_0+V$ with $H_0=\sum_jH_{0,j}$, $V=\sum_jV_j$ as in a local model:
--
--   1. the supports $B_j\subseteq[2n]$ contain at most $d$ Majorana labels, and each label lies in at most $q_B$ of them;
--   2. each $H_{0,j}$ is quadratic and supported in $B_j$, with $\|H_{0,j}\|\le 1$;
--   3. each $V_j$ is even and supported in $B_j$, with $\|V_j\|\le g$, $g\ge 0$;
--   4. $H_0$ and $V$ are Hermitian.
--
--   Let $\beta>0$, and let
--   $$
--   g_{\mathrm{mix}}=\frac{\min\{1/d,\frac12\log\frac{13}{12}\}}{2^dC_VI_\beta},\qquad C_V=q_B2^d,\qquad I_\beta=\int_0^{\beta/2}e^{dC_Hu}\,du,\qquad C_H=2q_B(d-1).
--   $$
--   If $g\le g_{\mathrm{mix}}$, then the Gibbs state is a convex mixture of even fermionic Gaussian states:
--   $$
--   \rho_\beta=\frac{e^{-\beta H}}{\operatorname{Tr}e^{-\beta H}}\in\operatorname{conv}(G_n).
--   $$
--   The threshold depends on $\beta,d,q_B$ only, not on $n$. Here $G_n$ contains rank-deficient and pure Gaussian states.
--
--   Differences from the source:
--   - generalization: supports B in balls of radius r0 of a lattice Λ ⊂ Z^D, with at most ν modes per site and each site in at most q_B sets → any finite family of supports B_j ⊆ [2n] with |B_j| ≤ d and each label in at most q_B of them; reason: the lattice enters only through d and q_B; a lattice family is one such family, since a label sits at one site
--   - generalization: g ≤ g_mix = η_mix/(2^d C_V I_β), η_mix = min{1/d, (1/2) log(13/12)} → BelowThreshold: d·η ≤ 1 and η ≤ (1/2) log(13/12) with η = 2^d C_V I_β g; reason: identical for d, q_B ≥ 1 and β > 0; for d = 0 or q_B = 0 the printed quotient is undefined and the product form reads 1/0 as +∞
--   - generalization: K0† = K0 and H a Hamiltonian → only the sums Σ H_{0,j} and Σ V_j are assumed Hermitian, not the local terms; reason: the Hermitian local terms of the page are a special case
--   - generalization: additive constants omitted from H, so X^∅ = 1 (B.81) → V_j may contain a scalar term (R = ∅ is even); reason: the page's case is scalar-free; a scalar does not change ρ_β or any coefficient with R ≠ ∅
--   - encoding: H0 = (1/4) γ^T K0 γ with K0^T = −K0, K0† = K0 (A.4) → H0 is the Hermitian sum of the quadratic local terms; K0 is not a binder; reason: K0 is determined by H0 (eq_A_9_A_10 states the identity)
--   - encoding: G_n, the even fermionic Gaussian states, rank-deficient and pure ones included → FermiCap.Gaussian.IsEvenGaussian: a density ρ = U ρ_λ U† with U = exp(iH₂), H₂ Hermitian quadratic, λ ∈ [−1,1]^n; reason: the standard definition of refs. [9, 10]; |λ_j| = 1 gives the rank-deficient and pure states
--   - encoding: Majorana operators γ_a satisfying (A.1) → the published Jordan–Wigner operators FermiCap.Gaussian.majorana, labels Fin (2 * n), 0-based; reason: any family with (A.1) on a 2^n-dimensional space is unitarily equivalent to this one, and all objects here are unitarily covariant
-- source:
--   Han, Zhao, Liu, Weakly interacting fermionic Gibbs states are Gaussian mixtures and classically simulable, arXiv:2609.35159v1, Theorem A.1, p. 10

import Mathlib
import Definitions.Def_FermiGaussMix_IsLocalModel
import Definitions.Def_FermiGaussMix_gibbs

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix FermiCap.Gaussian

namespace FermiGaussMix

/-- **Theorem A.1, p.10** (Han, Zhao, Liu, arXiv:2609.35159v1). For any system size and any Hamiltonian `H = H₀ + V` satisfying
(A.4)–(A.6), if `g ≤ g_mix`, then the Gibbs state `ρ_β = e^{-βH} / Tr e^{-βH}` lies in `conv(G_n)`.

**Formalization Note** The system is abstract: `n` modes, supports `B_j ⊆ [2n]` with at most `d` labels, each label in at most
`q_B` supports. `D` and `r₀` enter only through `d` and `q_B`, so "Fix `β`, `D`, `r₀`" is "for all `d`, `q_B`, `β`". The threshold
`g ≤ g_mix` is in product form (`BelowThreshold`), which does not mention `n`. `G_n` is `FermiCap.Gaussian.IsEvenGaussian`, including
rank-deficient and pure states. Hermiticity is assumed of the two sums `H₀`, `V`, not of the local terms. -/
theorem theorem_A_1 {n m d qB : ℕ} {g β : ℝ} {B : Fin m → Finset (Fin (2 * n))} {H0 V : Fin m → Op n}
    (hm : IsLocalModel d qB g B H0 V)
    (hH0 : (∑ j, H0 j)ᴴ = ∑ j, H0 j) (hV : (∑ j, V j)ᴴ = ∑ j, V j)
    (hβ : 0 < β) (hg : BelowThreshold d qB β g) :
    gibbs β (∑ j, H0 j + ∑ j, V j) ∈ convexHull ℝ {ρ : Op n | IsEvenGaussian ρ} := by sorry

end FermiGaussMix
