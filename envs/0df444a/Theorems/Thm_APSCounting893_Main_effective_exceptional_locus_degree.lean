-- Prove2me | Theorems.Thm_APSCounting893_Main_effective_exceptional_locus_degree
-- name    : APSCounting893.Main.effective_exceptional_locus_degree
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:24:11.592388+00:00
-- url     : https://prove2.me/theorems/64e02841-3fe0-47e1-b44b-24adf2e12eec
-- title:
--   Proposition 4.1 — Effective exceptional-locus degree
-- statement:
--   Let $F:\mathbb C^n\to\mathbb C^{n+1}$ be the reduced map, with $\dim Y=n\ge1$ and $d\ge\max(2,\deg f_i)$, and fix its finite surjective linear normalization. There exists a nonempty relative open set $U\subseteq Y$ over which the graph projection is finite and surjective, with
--
--   $$\deg(Y\setminus U)\le n d^{2n}.$$
--
--   The degree is the degree of the projective closure, determined by the Hilbert polynomial. The open set is an existential conclusion rather than an input oracle declaring the desired degree bound.
--
--   Differences from the source:
--   - encoding: the graph projection p and its good open subset → the polynomial map through the graph isomorphism, with local finite-module generation on principal opens; reason: the graph is canonically isomorphic to affine input space and has the same restricted projection
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), Proposition 4.1, p. 16, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_LineGeometry

set_option autoImplicit false

namespace APSCounting893.Main

theorem effective_exceptional_locus_degree (F : ReducedMap) (c : Affine ℂ F.n)
    (hc : IsNormalization (imageClosure F.F) c) :
    ∃ U : Set (Affine ℂ (F.n + 1)), GoodOpen F U ∧
      projectiveDegree (imageClosure F.F \ U) ≤ F.n * F.d ^ (2 * F.n) := by sorry

end APSCounting893.Main
