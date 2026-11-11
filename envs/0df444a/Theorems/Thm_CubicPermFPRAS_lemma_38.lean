-- Prove2me | Theorems.Thm_CubicPermFPRAS_lemma_38
-- name    : CubicPermFPRAS.lemma_38
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:57:59.535191+00:00
-- url     : https://prove2.me/theorems/65d49b20-d298-4cf0-b54f-2c977fdc042b
-- title:
--   Lemma 38, p.39 — $F(a)\le F_{\mathrm{aux}}(a)\le\frac43F(a)$
-- statement:
--   Let $\lambda$ be positive activities, $\alpha>1$, $r$ an anchor, $w(r,\cdot)$ $\alpha$-rough anchor weights, $B$ the rescaled matrix and $J=J_\alpha n^2$ with $J_\alpha\ge8\alpha^2$ (the standing assumptions of §8.1). For every $a>0$,
--   $$F(a)\le F_{\mathrm{aux}}(a)\le\frac43\,F(a),$$
--   where $F$ is the matching partition function and $F_{\mathrm{aux}}$ the normalizer of $\nu_a$.
--
--   Allowing crowded assignments thus changes the partition function by at most a constant factor.
--
--   Differences from the source: none.
-- source:
--   Chen, Guo, Vigoda, Yang, An Õ(n³)-time FPRAS for the Permanent, arXiv:2609.20717 (held version, sha256 9e14f335…), Lemma 38, p.39 (PDF 41)

import Mathlib
import Definitions.Def_CubicPermFPRAS_nuAux

set_option autoImplicit false

namespace CubicPermFPRAS

/-- **Lemma 38** (crowded assignments), p.39 (PDF 41), X. Chen, H. Guo, E. Vigoda, X. Yang, *An Õ(n³)-time FPRAS for the Permanent*, arXiv:2609.20717 (held version, sha256 9e14f335…).

Under the standing assumptions of §8.1 (positive activities `λ`, roughness parameter `α`, anchor
`r`, `α`-rough anchor weights, `J = J_α n²` with `J_α ≥ 8α²`), for every `a > 0`,
`F(a) ≤ F_aux(a) ≤ (4/3) F(a)`, where `F_aux` is the normalizer of Eq. (12) for the rescaled
matrix `B`.

**Formalization Note.** The §8.1 standing assumptions (p.37) are the binders. -/
theorem lemma_38 (n : ℕ) (hn : 1 ≤ n) (α : ℝ) (hα : 1 < α)
    (lam : Matrix (Fin n) (Fin n) ℝ) (hlam : ∀ u v, 0 < lam u v) (r : Fin n) (w : Fin n → ℝ)
    (hw : IsRoughAnchor α lam r w) (Jα : ℝ) (hJ : 8 * α ^ 2 ≤ Jα) (a : ℝ) (ha : 0 < a) :
    Fpoly (Bmat lam w) a ≤ Faux (Bmat lam w) (Jα * (n : ℝ) ^ 2) a ∧
      Faux (Bmat lam w) (Jα * (n : ℝ) ^ 2) a ≤ 4 / 3 * Fpoly (Bmat lam w) a := by sorry

end CubicPermFPRAS
