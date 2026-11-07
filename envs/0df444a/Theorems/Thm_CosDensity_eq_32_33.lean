-- Prove2me | Theorems.Thm_CosDensity_eq_32_33
-- name    : CosDensity.eq_32_33
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:40:07.931209+00:00
-- url     : https://prove2.me/theorems/5c38c4ae-6a13-416e-8791-5f2d11d9ae19
-- title:
--   (32)–(33) — the code responses $Z_i$ and $Z_q\ge Q$
-- statement:
--   Fix an integer $p>2$, unit codewords with nonnegative coordinates, a coloring, $z$ and $q$, and let $s$ be the vector sum of $P(z,q)$. Then the code responses $Z_i=\langle a_i,s\rangle$ are
--
--   $$Z_i=\gamma_p\sum_{r\in[N]}\langle a_i,a_r\rangle+Q\,\langle a_i,a_q\rangle,\qquad(32)$$
--
--   where $Q=L\sqrt m$, and $Z_q\ge Q$ (33).
--
--   The first term is Alice's response and the second Bob's; (33) gives the queried bit its signal.
--
--   Differences from the source:
--   - generalization: the §8 setting: N = m⌊c_N m^{ρ_p−1}⌋ bits, unit codewords in ℝ^m_{≥0}, a balanced coloring → every N and m and every coloring (balance not required); reason: the statement holds without these conditions; the paper's setting is an instance
--   - encoding: four mutually orthogonal blocks of dimension m with arbitrary orthonormal bases e_c, g_c, w_ℓ, and codewords in the code block → the space ℝ^{Fin 4 × Fin m}, block 0 = code, 1 = anchor, 2 = balancing, 3 = suffix, with the standard basis vectors; reason: every choice of the bases is isometric to this one and every statement depends only on inner products
--   - encoding: gadgets and streams are multisets / sequences → lists in a fixed order (levels ascending, |c_j| copies of the + vector then |c_j| copies of the − vector); reason: sums and M_p do not depend on the order
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.5, (32)–(33), p.33 (pdf_page 34)

import Mathlib
import Definitions.Def_CosDensity_Stream
import Definitions.Def_CosDensity_HardInstance

open scoped RealInnerProductSpace

namespace CosDensity

/-- **(32)–(33)**: the code responses of the hard stream. Q. Zhang, *Frequency Moments Beyond
Equality: Streaming Cosine Density Moments*, arXiv:2609.06925 (held version, sha256 f4d4df22…),
§8.5, (32) and (33), p.33 (pdf_page 34).

For unit codewords with nonnegative coordinates, every `z` and `q`, with `s` the vector sum of
`P(z, q)`, the code response is `Z_i = γ_p Σ_{r∈[N]} ⟨a_i, a_r⟩ + Q ⟨a_i, a_q⟩` (32) and
`Z_q ≥ Q` (33), where `Q = L √m`. -/
theorem eq_32_33 {N m : ℕ} (p : ℕ) (hp : 2 < p) (a : Fin N → EuclideanSpace ℝ (Fin m))
    (χ : Fin N → Fin m) (ha : IsUnitNonnegCode a) (z : Fin N → Bool) (q : Fin N) :
    (∀ i : Fin N, codeResp a i (hardStream p a χ z q).sum =
      gammaP p * ∑ r, ⟪a i, a r⟫ + queryAmp p m * ⟪a i, a q⟫) ∧
    queryAmp p m ≤ codeResp a q (hardStream p a χ z q).sum := by sorry

end CosDensity
