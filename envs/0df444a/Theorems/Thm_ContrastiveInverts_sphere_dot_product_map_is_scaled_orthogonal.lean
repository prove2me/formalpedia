-- Prove2me | Theorems.Thm_ContrastiveInverts_sphere_dot_product_map_is_scaled_orthogonal
-- name    : ContrastiveInverts.sphere_dot_product_map_is_scaled_orthogonal
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T18:43:22.446927+00:00
-- url     : https://prove2.me/theorems/eb3d6d2c-99d5-4949-9b65-b80744780848
-- title:
--   Proposition 2: extension of the Mazur-Ulam theorem to hyperspheres and the dot product
-- statement:
--   Let $N\ge1$, $r>0$, $Z=\mathbb{S}^{N-1}$ and $Z'=\mathbb{S}^{N-1}_r$. Let $h:\mathbb{R}^N\to Z'$ be differentiable on an open neighbourhood of $Z$, and suppose that on $Z$ it preserves the dot product up to the factor $r^2$:
--
--   $$r^2\,z^\top\tilde z=h(z)^\top h(\tilde z)\qquad\text{for all }z,\tilde z\in Z.$$
--
--   Then $h$ is an orthogonal linear transformation scaled by $r$ on $Z$: there is an orthogonal map $U$ of $\mathbb{R}^N$ such that $h(z)=r\,Uz$ for all $z\in Z$.
--
--   This is the step that turns preservation of the dot product into linearity.
-- source:
--   Zimmermann, Sharma, Schneider, Bethge and Brendel, Contrastive Learning Inverts the Data Generating Process, ICML 2021, arXiv:2102.08850v4, Section 3.2, Proposition 2, p. 4; restated with proof in Appendix A.1.2, Proposition 2, pp. 14-15

import Mathlib
import Definitions.Def_ContrastiveInverts_Basic

open MeasureTheory Filter Topology

namespace ContrastiveInverts

theorem sphere_dot_product_map_is_scaled_orthogonal {N : ℕ} (hN : 0 < N) (r : ℝ) (hr : 0 < r)
    (h : Vec N → Vec N) (hmap : ∀ x, h x ∈ Metric.sphere (0 : Vec N) r)
    (hdiff : ∃ U : Set (Vec N), IsOpen U ∧ Metric.sphere (0 : Vec N) 1 ⊆ U ∧
      DifferentiableOn ℝ h U)
    (hdot : ∀ z ∈ Metric.sphere (0 : Vec N) 1, ∀ z' ∈ Metric.sphere (0 : Vec N) 1,
      r ^ 2 * inner ℝ z z' = inner ℝ (h z) (h z')) :
    ∃ U : Vec N ≃ₗᵢ[ℝ] Vec N, ∀ z ∈ Metric.sphere (0 : Vec N) 1, h z = r • U z := by sorry

end ContrastiveInverts
