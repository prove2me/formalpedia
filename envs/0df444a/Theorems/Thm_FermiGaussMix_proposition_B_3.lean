-- Prove2me | Theorems.Thm_FermiGaussMix_proposition_B_3
-- name    : FermiGaussMix.proposition_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:01:53.097203+00:00
-- url     : https://prove2.me/theorems/fee65f79-2abc-409d-97ae-ee7b4c1b2d97
-- title:
--   Proposition B.3 — for $g\le g_{\mathrm{mix}}$, $XX^\dagger$ is a convex combination of nonnegative Gaussian operators
-- statement:
--   Let $H_0=\sum_jH_{0,j}$ and $V=\sum_jV_j$ come from a local model with Hermitian sums, let $\beta>0$, $T=\beta/2$ and $X=e^{TH_0}e^{-T(H_0+V)}$. If $g\le g_{\mathrm{mix}}$, then
--   $$
--   XX^\dagger=\sum_z\pi_z\sigma_z,\qquad\pi_z\ge 0,\quad\sum_z\pi_z=1,
--   $$
--   for finitely many nonnegative Gaussian operators $\sigma_z$. The middle operator of the factorization (B.1) thus already has the structure the theorem asks for.
--
--   Differences from the source:
--   - generalization: g ≤ g_mix = η_mix/(2^d C_V I_β), η_mix = min{1/d, (1/2) log(13/12)} → BelowThreshold: d·η ≤ 1 and η ≤ (1/2) log(13/12) with η = 2^d C_V I_β g; reason: identical for d, q_B ≥ 1 and β > 0; for d = 0 or q_B = 0 the printed quotient is undefined and the product form reads 1/0 as +∞
--   - generalization: supports B in balls of radius r0 of a lattice Λ ⊂ Z^D, with at most ν modes per site and each site in at most q_B sets → any finite family of supports B_j ⊆ [2n] with |B_j| ≤ d and each label in at most q_B of them; reason: the lattice enters only through d and q_B; a lattice family is one such family, since a label sits at one site
--   - generalization: K0† = K0 and H a Hamiltonian → only the sums Σ H_{0,j} and Σ V_j are assumed Hermitian, not the local terms; reason: the Hermitian local terms of the page are a special case
--   - generalization: additive constants omitted from H, so X^∅ = 1 (B.81) → V_j may contain a scalar term (R = ∅ is even); reason: the page's case is scalar-free; a scalar does not change ρ_β or any coefficient with R ≠ ∅
--   - encoding: a finite convex combination Σ_z π_z σ_z → membership in convexHull ℝ; reason: the real convex hull is the set of finite convex combinations
--   - encoding: G_n, the even fermionic Gaussian states, rank-deficient and pure ones included → FermiCap.Gaussian.IsEvenGaussian: a density ρ = U ρ_λ U† with U = exp(iH₂), H₂ Hermitian quadratic, λ ∈ [−1,1]^n; reason: the standard definition of refs. [9, 10]; |λ_j| = 1 gives the rank-deficient and pure states
--   - encoding: Majorana operators γ_a satisfying (A.1) → the published Jordan–Wigner operators FermiCap.Gaussian.majorana, labels Fin (2 * n), 0-based; reason: any family with (A.1) on a 2^n-dimensional space is unitarily equivalent to this one, and all objects here are unitarily covariant
-- source:
--   Han, Zhao, Liu, Weakly interacting fermionic Gibbs states are Gaussian mixtures and classically simulable, arXiv:2609.35159v1, Proposition B.3, p. 13; eq. (B.63), p. 18

import Mathlib
import Definitions.Def_FermiGaussMix_IsLocalModel
import Definitions.Def_FermiGaussMix_gibbs
import Definitions.Def_FermiGaussMix_IsPropagator

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix FermiCap.Gaussian

namespace FermiGaussMix

/-- **Proposition B.3, p.13** (Han, Zhao, Liu, arXiv:2609.35159v1). If `g ≤ g_mix`, then `X X†` is a convex combination of
nonnegative Gaussian operators, where `X = e^{T H₀} e^{-T H}` and `T = β/2`.

**Formalization Note** "Convex combination" is membership in the real convex hull, whose elements are the finite convex
combinations. -/
theorem proposition_B_3 {n m d qB : ℕ} {g β : ℝ} {B : Fin m → Finset (Fin (2 * n))} {H0 V : Fin m → Op n}
    (hm : IsLocalModel d qB g B H0 V)
    (hH0 : (∑ j, H0 j)ᴴ = ∑ j, H0 j) (hV : (∑ j, V j)ᴴ = ∑ j, V j)
    (hβ : 0 < β) (hg : BelowThreshold d qB β g) :
    xOp (β / 2) (∑ j, H0 j) (∑ j, V j) * (xOp (β / 2) (∑ j, H0 j) (∑ j, V j))ᴴ ∈
      convexHull ℝ {σ : Op n | IsNonnegGaussian σ} := by sorry

end FermiGaussMix
