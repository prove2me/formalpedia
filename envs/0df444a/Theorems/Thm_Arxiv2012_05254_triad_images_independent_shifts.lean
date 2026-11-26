-- Prove2me | Theorems.Thm_Arxiv2012_05254_triad_images_independent_shifts
-- name    : Arxiv2012_05254.triad_images_independent_shifts
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T04:42:39.735668+00:00
-- url     : https://prove2.me/theorems/18529694-d184-451e-82be-0dc6dab3f0fe
-- title:
--   Sec. 4.3: each triad image is the true image up to its own shift, and the shifts differ between triads
-- statement:
--   Let an array have elements at positions $x_0,\dots,x_{N-1}$ and true visibilities $V_{ab}$. Let the element gains have unit modulus, as after a priori flux-density calibration.
--
--   1. For every closed triad of non-collinear elements, the three-fringe image made from the corrupted visibilities $G_a^*G_bV_{ab}$ is the true three-fringe image of that triad, translated by a vector $t$ that depends on the triad.
--   2. These translations differ between triads in general. There are four elements, unit-modulus gains and visibilities such that no single translation works for both triads $(0,1,2)$ and $(0,2,3)$.
--
--   **Formalization Note** The paper's conclusion that summing such images "would not produce a coherent image" is not quantified and is not stated.
-- source:
--   Thyagarajan and Carilli, A Geometric View of Closure Phases in Interferometry, arXiv:2012.05254v3, Publ. Astron. Soc. Aust. 38 (2021), claim c037; Section 4.3, final paragraph, and Figs. 8-9, PDF p. 13

import Mathlib
import Definitions.Def_Arxiv2012_05254_Basic

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace Arxiv2012_05254

theorem triad_images_independent_shifts {N : ℕ} (x : Fin N → Plane) (V : Fin N → Fin N → ℂ)
    (G : Fin N → ℂ) (hG : ∀ a, ‖G a‖ = 1) :
    (∀ v : Fin 3 → Fin N, AffineIndependent ℝ (x ∘ v) →
      ∃ t : Plane, ∀ s : Plane, triadImage x (corruptVis G V) v s = triadImage x V v (s + t)) ∧
    ∃ (y : Fin 4 → Plane) (W : Fin 4 → Fin 4 → ℂ) (H : Fin 4 → ℂ), (∀ a, ‖H a‖ = 1) ∧
      AffineIndependent ℝ (y ∘ (![0, 1, 2] : Fin 3 → Fin 4)) ∧
      AffineIndependent ℝ (y ∘ (![0, 2, 3] : Fin 3 → Fin 4)) ∧
      ¬ ∃ t : Plane, ∀ s : Plane,
        triadImage y (corruptVis H W) ![0, 1, 2] s = triadImage y W ![0, 1, 2] (s + t) ∧
        triadImage y (corruptVis H W) ![0, 2, 3] s = triadImage y W ![0, 2, 3] (s + t) := by sorry

end Arxiv2012_05254
