-- Prove2me | Theorems.Thm_CosDensity_lemma_8_4
-- name    : CosDensity.lemma_8_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:32.418946+00:00
-- url     : https://prove2.me/theorems/0f68382e-d7e6-413f-8ba2-093fc08dff84
-- title:
--   Lemma 8.4 — gadget vectors are unit and pairwise nonnegative
-- statement:
--   Fix an integer $p>2$ and the constants of §8.3. Let $a_1,\dots,a_N\in\mathbb R^m$ be unit vectors with nonnegative coordinates and $\chi:[N]\to[m]$ a coloring. Then, for all $i,i'$, all levels $0\le j,k\le p$ and all signs $\sigma,\tau$,
--
--   $$\|u_{i,j,\sigma}\|=1\qquad\text{and}\qquad\langle u_{i,j,\sigma},u_{i',k,\tau}\rangle\ge 0 ,$$
--
--   where $u_{i,j,\sigma}=t_ja_i+\lambda e_{\chi(i)}+\sigma\mu_jg_{\chi(i)}$ is the vector (26).
--
--   So Alice's gadget vectors are legal inputs of the nonnegative-cosine regime.
--
--   Differences from the source:
--   - generalization: the §8 setting: N = m⌊c_N m^{ρ_p−1}⌋ bits, unit codewords in ℝ^m_{≥0}, a balanced coloring → every N and m and every coloring (balance not required); reason: the statement holds without these conditions; the paper's setting is an instance
--   - encoding: four mutually orthogonal blocks of dimension m with arbitrary orthonormal bases e_c, g_c, w_ℓ, and codewords in the code block → the space ℝ^{Fin 4 × Fin m}, block 0 = code, 1 = anchor, 2 = balancing, 3 = suffix, with the standard basis vectors; reason: every choice of the bases is isometric to this one and every statement depends only on inner products
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.4, p.31 (pdf_page 32): unit norm of (26) and Lemma 8.4

import Mathlib
import Definitions.Def_CosDensity_Stream
import Definitions.Def_CosDensity_HardInstance

open scoped RealInnerProductSpace

namespace CosDensity

/-- **Lemma 8.4**, with the unit-norm remark before it. Q. Zhang, *Frequency Moments Beyond
Equality: Streaming Cosine Density Moments*, arXiv:2609.06925 (held version, sha256 f4d4df22…),
§8.4, p.31 (pdf_page 32): "By construction, ‖u_{i,j,σ}‖ = 1" and "Lemma 8.4. Every pair of vectors
of the form (26) has nonnegative inner product."

For unit codewords with nonnegative coordinates and any coloring, every vector
`u_{i,j,σ} = t_j a_i + λ e_{χ(i)} + σ μ_j g_{χ(i)}` (`0 ≤ j ≤ p`) is a unit vector, and any two of
them have nonnegative inner product.

**Formalization Note.** `p > 2` and the §8.3 constants are fixed; `j, k` range over the levels
`0, …, p`. -/
theorem lemma_8_4 {N m : ℕ} (p : ℕ) (hp : 2 < p) (a : Fin N → EuclideanSpace ℝ (Fin m))
    (χ : Fin N → Fin m) (ha : IsUnitNonnegCode a) :
    (∀ (i i' : Fin N) (j k : ℕ) (σ τ : Bool), j ≤ p → k ≤ p →
      0 ≤ ⟪gadgetVec p a χ i j σ, gadgetVec p a χ i' k τ⟫) ∧
    ∀ (i : Fin N) (j : ℕ) (σ : Bool), j ≤ p → ‖gadgetVec p a χ i j σ‖ = 1 := by sorry

end CosDensity
