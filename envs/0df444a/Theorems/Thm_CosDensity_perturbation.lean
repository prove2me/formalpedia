-- Prove2me | Theorems.Thm_CosDensity_perturbation
-- name    : CosDensity.perturbation
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T11:38:30.559551+00:00
-- url     : https://prove2.me/theorems/eee1afc9-e6d6-4d9b-aef6-e7f8c1466887
-- title:
--   §8.8 — the perturbation $\tilde u=(\sqrt{1-\xi^2}u,\xi)$ and $\tilde D_i=(1-\xi^2)D_i+n\xi^2$
-- statement:
--   Let $u_1,\dots,u_n$ be unit vectors of $\mathbb R^\iota$ and $\xi\in[0,1]$, and let $\tilde u_i=(\sqrt{1-\xi^2}\,u_i,\ \xi)$. Then each $\tilde u_i$ is a unit vector,
--
--   $$\langle\tilde u_i,\tilde u_j\rangle=(1-\xi^2)\langle u_i,u_j\rangle+\xi^2,$$
--
--   which is at least $\xi^2$ when all $\langle u_i,u_j\rangle\ge0$, and the densities satisfy $\tilde D_i=(1-\xi^2)D_i+n\xi^2$.
--
--   The perturbation makes every similarity strictly positive while changing every density by a factor $1+o(1)$ in the paper's regime $\xi=m^{-2p}$.
--
--   Differences from the source:
--   - generalization: the hard stream in ℝ^{4m} with ξ = m^{−2p} → any stream of n unit vectors of ℝ^ι (ι finite) and any ξ ∈ [0, 1]; reason: the identities hold for every unit stream; the paper's case is an instance
--   - encoding: (1 + o(1)) conclusions for the densities and the moment → the exact identities; the asymptotic conclusions are carried by Theorem 8.1; reason: the o(1) statements are consequences of the exact identities at the paper's ξ
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.8, p.36 (pdf_page 37)

import Mathlib
import Definitions.Def_CosDensity_Stream
import Definitions.Def_CosDensity_Perturb

open scoped RealInnerProductSpace

namespace CosDensity

/-- **§8.8, the perturbation.** Q. Zhang, *Frequency Moments Beyond Equality: Streaming Cosine
Density Moments*, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.8, p.36 (pdf_page 37).

For a stream of `n` unit vectors `u_i` and `ξ ∈ [0, 1]`, the perturbed vectors
`ũ_i = (√(1 − ξ²) u_i, ξ)` are unit vectors with `⟨ũ_i, ũ_j⟩ = (1 − ξ²)⟨u_i, u_j⟩ + ξ²`, which is
at least `ξ²` when the `u_i` have pairwise nonnegative inner products, and the densities satisfy
`D̃_i = (1 − ξ²) D_i + n ξ²`.

**Formalization Note.** Streams are `Fin n → E` and densities `densityF`. The source space is
`EuclideanSpace ℝ ι` for any finite `ι` (the paper's `ℝ^{4m}`), the perturbed space
`EuclideanSpace ℝ (Option ι)`. `ξ ∈ [0, 1]` is arbitrary (the paper takes `ξ = m^{−2p}`); the
`(1 + o(1))` conclusions are carried by Theorem 8.1. -/
theorem perturbation {ι : Type*} [Fintype ι] {n : ℕ} (u : Fin n → EuclideanSpace ℝ ι)
    (hu : ∀ i, ‖u i‖ = 1) (ξ : ℝ) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) :
    (∀ i, ‖perturb ξ (u i)‖ = 1) ∧
    (∀ i j, ⟪perturb ξ (u i), perturb ξ (u j)⟫ = (1 - ξ ^ 2) * ⟪u i, u j⟫ + ξ ^ 2) ∧
    ((∀ i j, 0 ≤ ⟪u i, u j⟫) → ∀ i j, ξ ^ 2 ≤ ⟪perturb ξ (u i), perturb ξ (u j)⟫) ∧
    ∀ i, densityF (fun k => perturb ξ (u k)) i = (1 - ξ ^ 2) * densityF u i + n * ξ ^ 2 := by sorry

end CosDensity
