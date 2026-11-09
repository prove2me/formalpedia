-- Prove2me | Theorems.Thm_CosDensity_rationalization
-- name    : CosDensity.rationalization
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T11:38:41.163698+00:00
-- url     : https://prove2.me/theorems/6bc05407-b8d6-4a22-b6d8-f8a1bcaeedb9
-- title:
--   §8.8 — rationalization changes similarities by $\le2\eta$ and densities by $\le2n\eta$
-- statement:
--   Let $u_1,\dots,u_n$ be unit vectors of $\mathbb R^\iota$, $\xi\in[0,1]$, $\tilde u_i=(\sqrt{1-\xi^2}\,u_i,\ \xi)$, and let $\hat u_1,\dots,\hat u_n$ be unit vectors with $\|\hat u_i-\tilde u_i\|\le\eta$. Then for all $i,j$
--
--   $$|\langle\hat u_i,\hat u_j\rangle-\langle\tilde u_i,\tilde u_j\rangle|\le\|\hat u_i-\tilde u_i\|+\|\hat u_j-\tilde u_j\|\le2\eta,$$
--
--   and the densities before and after rationalization satisfy $|\hat D_i-\tilde D_i|\le2n\eta$.
--
--   With $\eta=m^{-6p}$ these errors are $o(1)$ and the rationalized stream keeps the constant gap.
--
--   Differences from the source:
--   - generalization: the perturbed hard stream with η = m^{−6p} and û from Lemma 8.10 → any unit stream u in ℝ^ι, any ξ ∈ [0, 1], any η and any unit vectors û with ‖û_i − ũ_i‖ ≤ η; reason: the bounds hold for every such family; the paper's case is an instance
--   - encoding: 2nη = o(1) → the exact bound 2nη; the asymptotic conclusion is carried by Theorem 8.1; reason: the o(1) is a consequence at the paper's η
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.8, pp.37–38 (pdf_page 38–39)

import Mathlib
import Definitions.Def_CosDensity_Stream
import Definitions.Def_CosDensity_Perturb

open scoped RealInnerProductSpace

namespace CosDensity

/-- **§8.8, the rationalization error.** Q. Zhang, *Frequency Moments Beyond Equality: Streaming
Cosine Density Moments*, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.8, pp.37–38
(pdf_page 38–39).

Let `ũ_i = (√(1 − ξ²) u_i, ξ)` be the perturbed vectors of a stream of `n` unit vectors `u_i`,
`ξ ∈ [0, 1]`, and let `û_i` be unit vectors with `‖û_i − ũ_i‖ ≤ η`. Then
`|⟨û_i, û_j⟩ − ⟨ũ_i, ũ_j⟩| ≤ ‖û_i − ũ_i‖ + ‖û_j − ũ_j‖ ≤ 2η`, and the densities before and after
rationalization satisfy `|D̂_i − D̃_i| ≤ 2nη`.

**Formalization Note.** Streams are `Fin n → E` and densities `densityF`. `ι` is any finite index
type (the paper's `ℝ^{4m}`); `ξ ∈ [0, 1]` and `η` are arbitrary (the paper takes `ξ = m^{−2p}`,
`η = m^{−6p}` and `û_i` from Lemma 8.10); the `o(1)` conclusions are carried by Theorem 8.1. -/
theorem rationalization {ι : Type*} [Fintype ι] {n : ℕ} (u : Fin n → EuclideanSpace ℝ ι)
    (hu : ∀ i, ‖u i‖ = 1) (ξ : ℝ) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) (η : ℝ)
    (uh : Fin n → EuclideanSpace ℝ (Option ι)) (huh : ∀ i, ‖uh i‖ = 1)
    (hη : ∀ i, ‖uh i - perturb ξ (u i)‖ ≤ η) :
    (∀ i j, |⟪uh i, uh j⟫ - ⟪perturb ξ (u i), perturb ξ (u j)⟫| ≤
      ‖uh i - perturb ξ (u i)‖ + ‖uh j - perturb ξ (u j)‖ ∧
      ‖uh i - perturb ξ (u i)‖ + ‖uh j - perturb ξ (u j)‖ ≤ 2 * η) ∧
    ∀ i, |densityF uh i - densityF (fun k => perturb ξ (u k)) i| ≤ 2 * n * η := by sorry

end CosDensity
