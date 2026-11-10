-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_exact_ellipsoid
-- name    : EdgeSublinearMWIS.Main.exact_ellipsoid
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T13:44:32.835845+00:00
-- url     : https://prove2.me/theorems/f601a7a3-d692-4315-91c1-e44d5702f272
-- title:
--   Exact rational ellipsoid feasibility for 0–1 hulls
-- statement:
--   There is one finite program for exact rational feasibility of any finite $0$–$1$ convex hull, given dimension and a polynomial bound on description coefficients, using a dialogue of valid strictly violated cuts. The polynomial description bound is also required to bound an actual finite halfspace description of every target hull. It has uniform polynomials for its query count, internal work and query bit lengths. Empty hulls and proper affine subspaces are included:
--   $$\text{empty output}\Longrightarrow P=\varnothing,$$
--   and a dialogue reaching its final permitted query must return a point of $P$ unless emptiness is certified. The program receives cut history rather than an ideal feasibility oracle or the vertices of $P$. This is the supporting implementation obligation explicitly invoked in §5.1; it is not an additional milestone.
--
--   Differences from the source:
--   - encoding: a deterministic polynomial-time algorithm on rational inputs → one finite program, serialized rational inputs and actual halting-step bounds; reason: binary conventions fix a computational model without restricting rational values
--   - encoding: exact rational ellipsoid with a strong separation oracle → a finite replayable transcript protocol with actual subprogram runs; reason: replaying polynomially many polynomial-length queries gives the same oracle feasibility guarantee and polynomial overhead
--   - generalization: the independent-set indicator hull P_r(G,k) used in Section 5.1 → every finite convex hull of Boolean vectors, with an actual polynomially bounded halfspace description; reason: the source invokes the generic exact-feasibility theorem and the 0-1 vertex description bound; every independent-set indicator hull is a binary hull
-- source:
--   Édouard Bonnet, Yeonsu Chang, STOC 2027 submission #1044 (October 2026), §5.1, GLS Theorem 6.4.1 and Lemma 6.2.4 as cited, p.15 (PDF p.15), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_Ellipsoid

namespace EdgeSublinearMWIS.Main

/-- Supporting exact rational feasibility obligation from §5.1, p.15 and GLS
Theorem 6.4.1 / Lemma 6.2.4, including lower-dimensional hulls. -/
theorem exact_ellipsoid :
    ∃ (E : Program) (bound queries work coordinates : Polynomial ℕ),
      ExactEllipsoid E bound queries work coordinates := by sorry

end EdgeSublinearMWIS.Main
