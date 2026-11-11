-- Prove2me | Theorems.Thm_CubicPermFPRAS_lemma_17
-- name    : CubicPermFPRAS.lemma_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:57:00.379699+00:00
-- url     : https://prove2.me/theorems/13233b6d-1809-483a-95bb-d82c271a1124
-- title:
--   Lemma 17, p.15 — $B(\mathcal N(u,v))\le2\alpha^2B(\mathcal P)$ and $B(\mathcal N(r,v))\ge\alpha^{-2}B(\mathcal P)$
-- statement:
--   Let $\lambda$ be positive edge activities on $K_{n,n}$, $r\in V_1$ an anchor, $\alpha>1$, and $w(r,\cdot)$ $\alpha$-rough anchor weights. The rescaled matrix $B$ of Eq. (10) satisfies, for every $u\in V_1$ and $v\in V_2$,
--   $$B(\mathcal N(u,v))\le2\alpha^2B(\mathcal P)\qquad\text{and}\qquad B(\mathcal N(r,v))\ge\alpha^{-2}B(\mathcal P).$$
--
--   The upper bound gives perfect matchings constant probability at the end of the activity schedule; both bounds enter the estimate on unmatched vertices.
--
--   Differences from the source: none.
-- source:
--   Chen, Guo, Vigoda, Yang, An Õ(n³)-time FPRAS for the Permanent, arXiv:2609.20717 (held version, sha256 9e14f335…), Lemma 17, p.15 (PDF 17); proof, p.38 (PDF 40)

import Mathlib
import Definitions.Def_CubicPermFPRAS_matchWeight

set_option autoImplicit false

namespace CubicPermFPRAS

/-- **Lemma 17** (near-perfect weights after rescaling), p.15 (PDF 17), X. Chen, H. Guo, E. Vigoda, X. Yang, *An Õ(n³)-time FPRAS for the Permanent*, arXiv:2609.20717 (held version, sha256 9e14f335…); proved on
p.38 (PDF 40).

For positive edge activities `λ`, an anchor `r` and `α`-rough anchor weights `w(r,·)`, the
rescaled matrix `B` of Eq. (10) satisfies, for every `u ∈ V₁` and `v ∈ V₂`,
`B(N(u,v)) ≤ 2α² B(P)` and `B(N(r,v)) ≥ α^{−2} B(P)`.

**Formalization Note.** The positivity of the activities and the `α`-roughness of the anchor
weights are the standing assumptions of §5.1 (p.11) and §8.1 (p.37); `α > 1` is the roughness
parameter of Lemma 8 (p.11). -/
theorem lemma_17 (n : ℕ) (hn : 1 ≤ n) (α : ℝ) (hα : 1 < α)
    (lam : Matrix (Fin n) (Fin n) ℝ) (hlam : ∀ u v, 0 < lam u v) (r : Fin n) (w : Fin n → ℝ)
    (hw : IsRoughAnchor α lam r w) :
    (∀ u v : Fin n,
      familyWeight (Bmat lam w) (NSet u v) ≤ 2 * α ^ 2 * familyWeight (Bmat lam w) (PSet n)) ∧
    ∀ v : Fin n,
      α⁻¹ ^ 2 * familyWeight (Bmat lam w) (PSet n) ≤ familyWeight (Bmat lam w) (NSet r v) := by sorry

end CubicPermFPRAS
