-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_convex_body_of_star_shaped_level_set
-- name    : BirkhoffGlobalSection.convex_body_of_star_shaped_level_set
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-02T08:20:04.37116+00:00
-- url     : https://prove2.me/theorems/12ffa721-055d-4986-80b4-05e06afab898
-- title:
--   Star-shaped level set with positive tangential Hessian bounds a convex body
-- statement:
--   Let $F:\mathbb{R}^4\to\mathbb{R}$ and let $S\subset\mathbb{R}^4$ be compact with $F=0$ and $dF\neq0$ on $S$, and with strictly positive tangential Hessian at every point of $S$:
--
--   $$dF_s\,v=0,\ v\neq0\ \Longrightarrow\ D^2F_s[v,v]>0 .$$
--
--   Assume $S$ is a radial graph over the round sphere $S^3$, with $F$ negative inside: every ray $\{r x : r>0\}$, $|x|=1$, meets $S$ exactly once, and if $Rx\in S$ then $F(rx)<0$ for $0\le r<R$. Then $S$ is the frontier of a compact convex body containing the origin in its interior:
--
--   $$\exists B\subset\mathbb{R}^4\ \text{compact, convex},\qquad 0\in\operatorname{int}B,\qquad S=\partial B .$$
--
--   This is a corrected form of `convex_body_of_regular_starshaped_hessian`, which is false as stated: a single point $S$ satisfies its hypotheses. Here the ray hypotheses force $S$ to be a hypersurface. Take $B=\{ts: s\in S,\ 0\le t\le1\}$. Convexity of $B$ is the Proved Hadamard-type theorem `star_shaped_level_set_convex`. The rest is topology: $\{ts: t<1\}$ is open, as the complement of the closed set $\{ts: t\ge1\}$.
-- source:
--   Classical (Hadamard-type convexity of a star-shaped hypersurface with positive second fundamental form); repair of the disproved platform statement convex_body_of_regular_starshaped_hessian (ff0375b2). Convexity part is the Proved platform theorem star_shaped_level_set_convex (fc05791e).

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Analysis.Convex.Basic

namespace BirkhoffGlobalSection

/-- A compact star-shaped zero level of `F` (every ray from the origin meets `S` exactly once,
with `F < 0` strictly before the hit), with nonzero gradient and positive tangential Hessian,
is the frontier of a compact convex body containing the origin in its interior. -/
theorem convex_body_of_star_shaped_level_set (F : Phase → ℝ) (S : Set Phase)
    (hS : IsCompact S)
    (hF0 : ∀ s ∈ S, F s = 0)
    (hreg : ∀ s ∈ S, fderiv ℝ F s ≠ 0)
    (hTH : HasPositiveTangentialHessianOn F S)
    (hray : ∀ x ∈ unitThreeSphere, ∃ r : ℝ, 0 < r ∧ (fun i : Fin 4 => r * x i) ∈ S)
    (huniq : ∀ x ∈ unitThreeSphere, ∀ r t : ℝ, 0 < r → 0 < t →
      (fun i : Fin 4 => r * x i) ∈ S → (fun i : Fin 4 => t * x i) ∈ S → r = t)
    (hneg : ∀ x ∈ unitThreeSphere, ∀ R : ℝ, 0 < R → (fun i : Fin 4 => R * x i) ∈ S →
      ∀ r : ℝ, 0 ≤ r → r < R → F (fun i : Fin 4 => r * x i) < 0) :
    ∃ B : Set Phase, IsCompact B ∧ Convex ℝ B ∧
      (0 : Phase) ∈ interior B ∧ S = frontier B := by sorry

end BirkhoffGlobalSection
