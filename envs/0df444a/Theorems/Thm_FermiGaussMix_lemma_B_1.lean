-- Prove2me | Theorems.Thm_FermiGaussMix_lemma_B_1
-- name    : FermiGaussMix.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:58:52.413193+00:00
-- url     : https://prove2.me/theorems/21366d74-0cbd-42b2-90f3-94fb50790fd0
-- title:
--   Lemma B.1 — the Gaussian sandwich $GBG/\operatorname{Tr}(GBG)\in\operatorname{conv}(G_n)$
-- statement:
--   Let $G$ be an invertible positive Gaussian operator, and let $B$ be a nonzero positive operator that can be written as
--   $$
--   B=\sum_z\pi_z\sigma_z,\qquad\pi_z\ge 0,\quad\sum_z\pi_z=1,
--   $$
--   with every $\sigma_z$ a nonnegative Gaussian operator. Then
--   $$
--   \frac{GBG}{\operatorname{Tr}(GBG)}\in\operatorname{conv}(G_n).
--   $$
--   This transfers a decomposition of $XX^\dagger$ to the normalized Gibbs state.
--
--   Differences from the source:
--   - encoding: G an invertible positive Gaussian operator → G.PosDef and IsNonnegGaussian G; reason: a positive definite matrix is invertible, and a positive Gaussian operator is a nonnegative multiple of a Gaussian state
--   - encoding: a finite convex combination Σ_z π_z σ_z → membership in convexHull ℝ; reason: the real convex hull is the set of finite convex combinations
--   - encoding: G_n, the even fermionic Gaussian states, rank-deficient and pure ones included → FermiCap.Gaussian.IsEvenGaussian: a density ρ = U ρ_λ U† with U = exp(iH₂), H₂ Hermitian quadratic, λ ∈ [−1,1]^n; reason: the standard definition of refs. [9, 10]; |λ_j| = 1 gives the rank-deficient and pure states
--   - encoding: Majorana operators γ_a satisfying (A.1) → the published Jordan–Wigner operators FermiCap.Gaussian.majorana, labels Fin (2 * n), 0-based; reason: any family with (A.1) on a 2^n-dimensional space is unitarily equivalent to this one, and all objects here are unitarily covariant
-- source:
--   Han, Zhao, Liu, Weakly interacting fermionic Gibbs states are Gaussian mixtures and classically simulable, arXiv:2609.35159v1, Lemma B.1, p. 11

import Mathlib
import Definitions.Def_FermiGaussMix_gibbs

open scoped BigOperators ComplexOrder
open Matrix FermiCap.Gaussian

namespace FermiGaussMix

/-- **Lemma B.1, p.11** (Han, Zhao, Liu, arXiv:2609.35159v1). Let `G` be an invertible positive Gaussian operator, and let
`B` be a nonzero positive operator that is a convex combination of nonnegative Gaussian operators. Then
`G B G / Tr(G B G) ∈ conv(G_n)`.

**Formalization Note** `conv(G_n)` is the real convex hull of `FermiCap.Gaussian.IsEvenGaussian`, which contains the
rank-deficient states, as the page requires. The finite family (B.2) is membership in the convex hull. -/
theorem lemma_B_1 {n : ℕ} {G B : Op n} (hG : G.PosDef) (hGG : IsNonnegGaussian G)
    (hB : B.PosSemidef) (hB0 : B ≠ 0) (hconv : B ∈ convexHull ℝ {σ : Op n | IsNonnegGaussian σ}) :
    ((G * B * G).trace)⁻¹ • (G * B * G) ∈ convexHull ℝ {ρ : Op n | IsEvenGaussian ρ} := by sorry

end FermiGaussMix
