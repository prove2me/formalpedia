-- Prove2me | Theorems.Thm_CliffordCert_Optimal_ordinary_subspace_cover
-- name    : CliffordCert.Optimal.ordinary_subspace_cover
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:34:24.49721+00:00
-- url     : https://prove2.me/theorems/9a3ffaa3-892c-4577-8aa2-cf58f966d2d6
-- title:
--   Lemma 7 — ordinary binary subspace cover
-- statement:
--   Let $1\le k\le N$ be integers. There is a list of $k$-dimensional subspaces of $V=\mathbb F_2^N$ such that
--   $$V=\bigcup_{W\text{ in the list}}W,\qquad L_0\le2\cdot2^{N-k}.$$
--   Intersections are allowed. This is the ordinary cover used before imposing symplectic nondegeneracy.
--
--   Differences from the source:
--   - encoding: an arbitrary N-dimensional binary vector space → Fin N → ZMod 2 with an arbitrary alternating nondegenerate bilinear form when needed; reason: choosing coordinates is a linear isomorphism and changes no instance
-- source:
--   Hyunho Cha, Jungwoo Lee, STOC 2027 submission #226 (October 2026), p. 12, Lemma 7 (PDF p. 13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/226.pdf

import Definitions.Def_CliffordCert_Optimal_symplectic
set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal

namespace CliffordCert.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem ordinary_subspace_cover (N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) :
    ∃ W : List (Submodule F₂ (Binary N)),
      IsKCover k W ∧ W.length ≤ 2 * 2^(N-k) := by sorry
end CliffordCert.Optimal
