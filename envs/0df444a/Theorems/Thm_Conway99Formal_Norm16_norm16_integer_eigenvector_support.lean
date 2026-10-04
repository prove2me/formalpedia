-- Prove2me | Theorems.Thm_Conway99Formal_Norm16_norm16_integer_eigenvector_support
-- name    : Conway99Formal.Norm16.norm16_integer_eigenvector_support
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T01:56:22.710996+00:00
-- url     : https://prove2.me/theorems/db548100-8401-44c7-b15d-ade71f29df91
-- title:
--   Equal sign supports of a norm-sixteen integer eigenvector
-- statement:
--   Let $G$ be a finite simple graph with strongly regular parameters $(99,14,1,2)$, and let $a:V(G)\to\mathbb Z$ be an integer vector satisfying the eigenrelation $Aa=-4a$ in the actual vertex coordinates of $G$. If its squared Euclidean norm is $16$, then exactly eight vertices have coordinate $+1$ and exactly eight have coordinate $-1$. The theorem does not assume or assert that such a vector exists in every graph with these parameters.
-- source:
--   Formalization in `formalization/2026-10-03/norm16-geometry/Norm16Geometry.lean`, source revision `a45708acebe3f397faccb1b646be906f24f23ee5` (SHA-256 `b83a93ee0fc9db04974b574eda0c48c9e82eeab8477082d47e6ab02aa66005d9`), theorem `Conway99Formal.Norm16.norm16_support_card`. This is the accepted integer minus-four minimum argument in `archive/clean-start/proof-library.zip`, member `proofs/INTEGER_MINUS_FOUR_MINIMUM.md` (SHA-256 `8ad639473c3d1e73eed4bec9a23161b1cd7d524f95a1bf2c507cf60081a31789`), specialized to norm sixteen. The source package records further accepted zero-geometry and cross-design claims, but they are not premises or conclusions here. Formal novelty QA passed as run `run-24ffe37f1c61` on integration revision `a45708acebe3f397faccb1b646be906f24f23ee5`; the final standalone candidate wrapper is submitted for coordinator compilation. Packaged standalone solution SHA-256 `dd61a715bd3061f8bbdd4683e12b0d90d71fa852d33874326d8b8ef34f9b3838`.

import Mathlib
set_option autoImplicit false

theorem Conway99Formal.Norm16.norm16_integer_eigenvector_support
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) (a : V → ℤ)
    (ha : ∀ v, (∑ u : V, G.adjMatrix ℤ v u * a u) = -4 * a v)
    (hnorm : (∑ v : V, a v * a v) = 16) :
    (Finset.univ.filter (fun v => a v = 1)).card = 8 ∧
      (Finset.univ.filter (fun v => a v = -1)).card = 8 := by sorry
