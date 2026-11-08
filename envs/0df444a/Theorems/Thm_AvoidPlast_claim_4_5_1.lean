-- Prove2me | Theorems.Thm_AvoidPlast_claim_4_5_1
-- name    : AvoidPlast.claim_4_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:38:23.741589+00:00
-- url     : https://prove2.me/theorems/ca266533-dc60-4b1f-8b41-29ba9ac076be
-- title:
--   Claim 4.5.1 — distance of the composed polynomial
-- statement:
--   Let $\tilde x:F^{m_1}\to F$, let $\tilde y,\tilde y^*:[m_1+1]\to(F^{m_2}\to F)$, let $\tilde p$ and $\tilde p^*$ be defined by Eq. (4.1) from $\tilde y$ and $\tilde y^*$, and let each field element be written in $w\le3\log n$ bits. If the bit-strings of $\tilde y$ and $\tilde y^*$ are $\delta$-close in relative Hamming distance, then the bit-strings of $\tilde p$ and $\tilde p^*$ are $\delta_1$-close, where
--
--   $$\delta_1=(m_1+1)(3\log n)\delta.$$
--
--   This is the step of the soundness of Theorem 4.1 that transfers proximity to the composed polynomial.
--
--   Differences from the source:
--   - generalization: $\tilde x$ the low-degree extension of $x$; $\tilde y^*$ a low-degree codeword; elements in exactly $3\log n$ bits → arbitrary $\tilde x$, $\tilde y$, $\tilde y^*$; elements in $w\le3\log n$ bits under any injective code; reason: the page's proof uses only the composition structure; the paper's objects are an instance
--   - reading: $\log n$ → $\log_2n$; reason: the binary logarithm, since it counts bits in Section 4.2
--   - encoding: $\delta$-close → relative distance at most $\delta$; reason: the page's usage: Hamming distance as bit-strings
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Claim 4.5.1, p.20

import Mathlib
import Definitions.Def_AvoidPlast_relDist
import Definitions.Def_AvoidPlast_composedPoly

namespace AvoidPlast

/-- Claim 4.5.1 (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), p.20): if the bit-strings of `ỹ` and `ỹ*` are `δ`-close, with each field element
written in `w ≤ 3 log n` bits, then the bit-strings of `p̃` and `p̃*` (Eq. (4.1)) are
`(m₁ + 1)(3 log n)δ`-close in relative Hamming distance.

**Formalization Note** Stated for arbitrary `x̃`, `ỹ`, `ỹ*`, which is all the page's proof uses. -/
theorem claim_4_5_1 {F : Type} [Field F] [Fintype F] (w n m₁ m₂ : ℕ)
    (hw : (w : ℝ) ≤ 3 * Real.logb 2 n) (code : F → Fin w → Bool)
    (hcode : Function.Injective code) (xt : (Fin m₁ → F) → F)
    (y ys : Fin (m₁ + 1) → (Fin m₂ → F) → F) (δ : ℝ)
    (hclose : relDist (fun a : Fin (m₁ + 1) × (Fin m₂ → F) × Fin w => code (y a.1 a.2.1) a.2.2)
      (fun a => code (ys a.1 a.2.1) a.2.2) ≤ δ) :
    relDist (fun a : (Fin m₂ → F) × Fin w => code (composedPoly xt y a.1) a.2)
      (fun a => code (composedPoly xt ys a.1) a.2) ≤
      ((m₁ : ℝ) + 1) * (3 * Real.logb 2 n) * δ := by sorry

end AvoidPlast
