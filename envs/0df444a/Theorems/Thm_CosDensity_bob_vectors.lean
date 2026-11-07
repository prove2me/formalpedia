-- Prove2me | Theorems.Thm_CosDensity_bob_vectors
-- name    : CosDensity.bob_vectors
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:42.434505+00:00
-- url     : https://prove2.me/theorems/27f914ad-ea7c-47ae-a5f1-0a3e07d9acf6
-- title:
--   §8.5 — Bob's vectors are unit, and $P(z,q)$ has nonnegative cosines
-- statement:
--   Fix an integer $p>2$, unit codewords $a_1,\dots,a_N\in\mathbb R^m$ with nonnegative coordinates, a coloring and a query $q$. Bob's vectors $v_\ell=\frac1{\sqrt m}a_q+\sqrt{1-\frac1m}\,w_\ell$ satisfy
--
--   1. $\|v_\ell\|=1$;
--   2. $\langle v_\ell,v_r\rangle=1$ if $\ell=r$ and $1/m$ if $\ell\ne r$;
--   3. $\langle v_\ell,u_{i,j,\sigma}\rangle=\dfrac{t_j}{\sqrt m}\langle a_q,a_i\rangle\ge0$;
--   4. consequently every hard stream $P(z,q)$ is a stream of unit vectors with pairwise nonnegative inner products.
--
--   So the reduction's inputs satisfy the nonnegative-cosine promise.
--
--   Differences from the source:
--   - generalization: the §8 setting: N = m⌊c_N m^{ρ_p−1}⌋ bits, unit codewords in ℝ^m_{≥0}, a balanced coloring → every N and m and every coloring (balance not required); reason: the statement holds without these conditions; the paper's setting is an instance
--   - encoding: four mutually orthogonal blocks of dimension m with arbitrary orthonormal bases e_c, g_c, w_ℓ, and codewords in the code block → the space ℝ^{Fin 4 × Fin m}, block 0 = code, 1 = anchor, 2 = balancing, 3 = suffix, with the standard basis vectors; reason: every choice of the bases is isometric to this one and every statement depends only on inner products
--   - encoding: gadgets and streams are multisets / sequences → lists in a fixed order (levels ascending, |c_j| copies of the + vector then |c_j| copies of the − vector); reason: sums and M_p do not depend on the order
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.5, p.33 (pdf_page 34)

import Mathlib
import Definitions.Def_CosDensity_Stream
import Definitions.Def_CosDensity_HardInstance

open scoped RealInnerProductSpace

namespace CosDensity

/-- **Bob's vectors.** Q. Zhang, *Frequency Moments Beyond Equality: Streaming Cosine Density
Moments*, arXiv:2609.06925 (held version, sha256 f4d4df22…), §8.5, p.33 (pdf_page 34).

For unit codewords with nonnegative coordinates and a query `q`, each
`v_ℓ = (1/√m) a_q + √(1 − 1/m) w_ℓ` is a unit vector, `⟨v_ℓ, v_r⟩` is `1` if `ℓ = r` and `1/m`
otherwise, `⟨v_ℓ, u_{i,j,σ}⟩ = (t_j/√m) ⟨a_q, a_i⟩ ≥ 0`; thus Bob's vectors preserve the
nonnegative-cosine promise: every stream `P(z, q)` of (34) is a unit stream with pairwise
nonnegative cosines. -/
theorem bob_vectors {N m : ℕ} (p : ℕ) (hp : 2 < p) (a : Fin N → EuclideanSpace ℝ (Fin m))
    (χ : Fin N → Fin m) (ha : IsUnitNonnegCode a) (q : Fin N) :
    (∀ ℓ : Fin m, ‖bobVec a q ℓ‖ = 1) ∧
    (∀ ℓ r : Fin m, ⟪bobVec a q ℓ, bobVec a q r⟫ = if ℓ = r then 1 else 1 / (m : ℝ)) ∧
    (∀ (ℓ : Fin m) (i : Fin N) (j : ℕ) (σ : Bool),
      ⟪bobVec a q ℓ, gadgetVec p a χ i j σ⟫ = level p j / Real.sqrt m * ⟪a q, a i⟫ ∧
        0 ≤ level p j / Real.sqrt m * ⟪a q, a i⟫) ∧
    ∀ z : Fin N → Bool,
      IsUnitStream (hardStream p a χ z q) ∧ NonnegCosine (hardStream p a χ z q) := by sorry

end CosDensity
