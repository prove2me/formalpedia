-- Prove2me | Theorems.Thm_CubicProductLB_lemma_16
-- name    : CubicProductLB.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:18:46.768116+00:00
-- url     : https://prove2.me/theorems/6d25beb3-5d85-4eaa-9ea8-df3e3e57c4ea
-- title:
--   Lemma 16 — 2-simple functions have zero full coefficient
-- statement:
--   If $g : \{0,1\}^M \to \mathbb F_2$ is 2-simple, then its full multilinear coefficient vanishes:
--   $$\widehat g([M]) = 0.$$
--   Together with Lemma 17 this gives the algebraic obstruction of the argument.
--
--   Differences from the source: none.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Lemma 16, Eq. (262), p.31

import Mathlib
import Definitions.Def_CubicProductLB_IsTwoSimple
import Definitions.Def_CubicProductLB_IsMultilinearRep

namespace CubicProductLB

/-- Lemma 16 (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Lemma 16, Eq. (262), p.31). A 2-simple function has zero full multilinear
coefficient. -/
theorem lemma_16 {M : ℕ} (g : (Fin M → Bool) → ZMod 2) (hg : IsTwoSimple g)
    (c : Finset (Fin M) → ZMod 2) (hc : IsMultilinearRep g c) : c Finset.univ = 0 := by sorry

end CubicProductLB
