-- Prove2me | Theorems.Thm_CosDensity_eq_31
-- name    : CosDensity.eq_31
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:56.409216+00:00
-- url     : https://prove2.me/theorems/e0014e46-d641-4922-98f9-b7fb23727926
-- title:
--   (31) — Alice's prefix sum is independent of $z$ and has no balancing component
-- statement:
--   Fix an integer $p>2$. For every bit string $z\in\{0,1\}^N$, the vector sum of Alice's prefix $\biguplus_{i}\mathcal G_{z_i}(a_i)$ is
--
--   $$s_A=\gamma_p\sum_{i\in[N]}a_i+\beta_p\sum_{i\in[N]}e_{\chi(i)},\qquad(31)$$
--
--   independent of $z$; in particular $\langle g_c,s_A\rangle=0$ for every color $c$.
--
--   Differences from the source:
--   - generalization: the §8 setting: N = m⌊c_N m^{ρ_p−1}⌋ bits, unit codewords in ℝ^m_{≥0}, a balanced coloring → every N and m, every family of codewords and every coloring; reason: the statement holds without these conditions; the paper's setting is an instance
--   - encoding: four mutually orthogonal blocks of dimension m with arbitrary orthonormal bases e_c, g_c, w_ℓ, and codewords in the code block → the space ℝ^{Fin 4 × Fin m}, block 0 = code, 1 = anchor, 2 = balancing, 3 = suffix, with the standard basis vectors; reason: every choice of the bases is isometric to this one and every statement depends only on inner products
--   - encoding: gadgets and streams are multisets / sequences → lists in a fixed order (levels ascending, |c_j| copies of the + vector then |c_j| copies of the − vector); reason: sums and M_p do not depend on the order
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.5, (31), p.32 (pdf_page 33)

import Mathlib
import Definitions.Def_CosDensity_Stream
import Definitions.Def_CosDensity_HardInstance

open scoped RealInnerProductSpace

namespace CosDensity

/-- **(31)**: Alice's prefix sum. Q. Zhang, *Frequency Moments Beyond Equality: Streaming Cosine
Density Moments*, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.5, (31), p.32
(pdf_page 33).

For every bit string `z`, the vector sum of Alice's prefix `⊎_i G_{z_i}(a_i)` is
`s_A = γ_p Σ_i a_i + β_p Σ_i e_{χ(i)}`, independent of `z`; in particular it has no balancing
component. -/
theorem eq_31 {N m : ℕ} (p : ℕ) (hp : 2 < p) (a : Fin N → EuclideanSpace ℝ (Fin m))
    (χ : Fin N → Fin m) (z : Fin N → Bool) :
    (alicePrefix p a χ z).sum =
        gammaP p • ∑ i, codeVec (a i) + betaP p • ∑ i, anchorVec (χ i) ∧
    ∀ c : Fin m, ⟪balVec c, (alicePrefix p a χ z).sum⟫ = 0 := by sorry

end CosDensity
