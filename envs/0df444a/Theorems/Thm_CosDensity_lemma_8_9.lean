-- Prove2me | Theorems.Thm_CosDensity_lemma_8_9
-- name    : CosDensity.lemma_8_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:40:13.538124+00:00
-- url     : https://prove2.me/theorems/e1b7ec86-1b79-4122-949c-9f6705e63f4d
-- title:
--   Lemma 8.9 — $M_p(P(z,q))=V_0(q)+\kappa_p\sum_{i:z_i=1}Z_i^p$
-- statement:
--   Fix an integer $p>2$, unit codewords with nonnegative coordinates and a coloring. For every $z\in\{0,1\}^N$ and every $q\in[N]$,
--
--   $$M_p(P(z,q))=V_0(q)+\kappa_p\sum_{i:\,z_i=1}Z_i^p,$$
--
--   where $Z_i$ is the code response of the vector sum of $P(z,q)$.
--
--   The moment is the global baseline plus an independent contribution from each bit set to $1$.
--
--   Differences from the source:
--   - generalization: the §8 setting: N = m⌊c_N m^{ρ_p−1}⌋ bits, unit codewords in ℝ^m_{≥0}, a balanced coloring → every N and m, every coloring (balance not required), and no (35)–(36); reason: the statement holds without these conditions; the paper's setting is an instance
--   - encoding: four mutually orthogonal blocks of dimension m with arbitrary orthonormal bases e_c, g_c, w_ℓ, and codewords in the code block → the space ℝ^{Fin 4 × Fin m}, block 0 = code, 1 = anchor, 2 = balancing, 3 = suffix, with the standard basis vectors; reason: every choice of the bases is isometric to this one and every statement depends only on inner products
--   - encoding: gadgets and streams are multisets / sequences → lists in a fixed order (levels ascending, |c_j| copies of the + vector then |c_j| copies of the − vector); reason: sums and M_p do not depend on the order
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.7, Lemma 8.9, p.35 (pdf_page 36)

import Mathlib
import Definitions.Def_CosDensity_Stream
import Definitions.Def_CosDensity_HardInstance

open scoped RealInnerProductSpace

namespace CosDensity

/-- **Lemma 8.9** (the moment decomposes bit by bit). Q. Zhang, *Frequency Moments Beyond
Equality: Streaming Cosine Density Moments*, arXiv:2609.06925 (held version, sha256 f4d4df22…),
§8.7, Lemma 8.9, p.35 (pdf_page 36).

For every `z ∈ {0,1}^N` and every `q ∈ [N]`, `M_p(P(z, q)) = V₀(q) + κ_p Σ_{i : z_i = 1} Z_i^p`,
where `Z_i` is the code response of the vector sum of `P(z, q)`.

**Formalization Note.** Stated for every `N`, `m`, every code of unit vectors with nonnegative
coordinates and every coloring; the balance of the coloring and the relation
`N = m ⌊c_N m^{ρ_p−1}⌋` are not needed. -/
theorem lemma_8_9 {N m : ℕ} (p : ℕ) (hp : 2 < p) (a : Fin N → EuclideanSpace ℝ (Fin m))
    (χ : Fin N → Fin m) (ha : IsUnitNonnegCode a) (z : Fin N → Bool) (q : Fin N) :
    moment p (hardStream p a χ z q) =
      baseline p a χ q +
        kappa p * ∑ i ∈ Finset.univ.filter (fun i => z i = true),
          codeResp a i (hardStream p a χ z q).sum ^ p := by sorry

end CosDensity
