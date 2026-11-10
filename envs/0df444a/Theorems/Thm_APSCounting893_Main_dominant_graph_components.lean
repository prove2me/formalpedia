-- Prove2me | Theorems.Thm_APSCounting893_Main_dominant_graph_components
-- name    : APSCounting893.Main.dominant_graph_components
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:24:35.164767+00:00
-- url     : https://prove2.me/theorems/1b1cd5bf-5b86-4a06-870b-034d8ab295fd
-- title:
--   Proposition 4.2 — Dominant graph components
-- statement:
--   In the reduced-map setup fix a normalization, good open set $U$, and nonzero direction $\alpha$ whose line $L$ meets $V=\mathbb C^n\setminus\pi(Y\setminus U)$. Put $\beta=\pi\circ p$ and $D=\overline{\beta^{-1}(L\cap V)}$ inside the graph. Every irreducible component $D'$ satisfies
--
--   $$\overline{\beta(D')}=L,\qquad [\mathbb C(D'):\mathbb C(L)]<\infty.$$
--
--   The extension is the actual component function field over the line parameter, with the inclusion fixed on constants and $t$. No finite-extension certificate is assumed as input.
--
--   Differences from the source:
--   - encoding: the closed curve inside the graph → its image in input coordinates under the graph isomorphism; reason: Zariski closure, components and function fields are transported by this isomorphism
--   - encoding: the induced inclusion of line function fields → an algebra structure on the fraction field of the actual coordinate ring, pinned on constants and the line parameter; reason: expresses the unique induced function-field map without assuming its finiteness
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), Proposition 4.2, p. 17, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_LineGeometry

set_option autoImplicit false

namespace APSCounting893.Main

theorem dominant_graph_components (F : ReducedMap) (D : LineData F) (W : Set (Affine ℂ F.n))
    (hW : AffineComponent (closedGraphCurve F D.c D.alpha D.U) W) :
    RSCapacity.zClosure (evaluate (betaPolynomials F D.c) '' W) = affineLine 0 D.alpha ∧
      FiniteLineFunctionField F D W := by sorry

end APSCounting893.Main
