-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_body_of_regular_starshaped_hessian
-- name    : BirkhoffGlobalSection.convex_body_of_regular_starshaped_hessian
-- status  : Disproved
-- author  : @caleb
-- created : 2026-10-01T19:07:13.049986+00:00
-- url     : https://prove2.me/theorems/ff0375b2-ded3-4e3f-ba7d-fc04c58bf629
-- title:
--   Convex body from a regular star-shaped level with positive Hessian
-- statement:
--   Let $H$ be a real-valued function on $\mathbb{R}^4$ and $S \subset \mathbb{R}^4$ a subset with
--
--   $$S \text{ compact and connected}, \qquad H = 0 \text{ on } S, \qquad dH_y \ne 0 \text{ on } S, \qquad dH_y\,y > 0 \text{ on } S,$$
--
--   and suppose $H$ has strictly positive tangential Hessian at every point of $S$:
--
--   $$dH_y\,v = 0,\ v \ne 0 \quad\Longrightarrow\quad D^2H_y[v,v] > 0 \qquad (y \in S).$$
--
--   Then $S$ is the boundary of a compact convex body containing the origin in its interior:
--
--   $$B \subset \mathbb{R}^4 \text{ compact and convex}, \qquad 0 \in \mathrm{int}\, B, \qquad \partial B = S.$$
--
--   Regularity presents $S$ as a smooth hypersurface, radial transversality plus compactness present it as a graph over the sphere (hence the boundary of a star-shaped domain), and Hessian positivity makes the second fundamental form positive definite, so the enclosed domain is convex. Connectedness is essential: without it $S$ could be a union of concentric spheres.
--
--   This is the abstract criterion that turns the analytic estimates on an energy component (regularity, radial transversality, tangential-Hessian positivity) into the geometric convex body. It applies to any Hamiltonian and level component, not only the elliptic-hyperbolic one.
--
--   **Formalization Note** Lean states differentiability through the Fréchet derivative $fderiv$ (which vanishes exactly at non-differentiable points, so the regularity hypothesis also forces differentiability on $S$). Connectedness is stated as `IsConnected`, which includes nonemptiness.
-- source:
--   Abstracted from the proof of Theorem 9.4(ii) in Liu--Salomao, https://arxiv.org/html/2506.17867v2#S9.SS3 (completion of Theorem 1.12 in Section 9.4): the regularity, radial-transversality and tangential-Hessian estimates on the compact level component are exactly what yield the convex body. Classical background: a compact hypersurface with positive definite second fundamental form bounds a convex domain (level-set identity relating the second fundamental form to the tangential Hessian).

import Definitions.Def_BirkhoffGlobalSection

open BirkhoffGlobalSection

theorem BirkhoffGlobalSection.convex_body_of_regular_starshaped_hessian
    (H : Phase → ℝ) (S : Set Phase)
    (hcompact : IsCompact S)
    (hconn : IsConnected S)
    (hreg : ∀ y ∈ S, fderiv ℝ H y ≠ 0)
    (hstar : ∀ y ∈ S, 0 < fderiv ℝ H y y)
    (hzero : ∀ y ∈ S, H y = 0)
    (hhess : HasPositiveTangentialHessianOn H S) :
    ∃ B : Set Phase, IsCompact B ∧ Convex ℝ B ∧
      (0 : Phase) ∈ interior B ∧ S = frontier B := by sorry
