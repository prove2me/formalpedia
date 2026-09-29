-- Prove2me | Theorems.Thm_FamousTheorems_inscribed_angle_converse_concyclic_7a
-- name    : FamousTheorems.inscribed_angle_converse_concyclic_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:27:37.642813+00:00
-- url     : https://prove2.me/theorems/3057525b-965a-43a5-bd6a-b63287bead7d
-- title:
--   Converse of the inscribed angle theorem (concyclicity criterion)
-- statement:
--   **Converse of the inscribed angle theorem.** Let $p_1,p_2,p_3,p_4$ be points in an oriented Euclidean plane with $p_1,p_2,p_4$ not collinear. If the oriented angles satisfy
--   $$2\,\angle p_1p_2p_4=2\,\angle p_1p_3p_4\pmod{2\pi},$$
--   then $p_1,p_2,p_3,p_4$ lie on a common circle.
--
--   This concyclicity criterion is used constantly in olympiad geometry. Doubled oriented angles make one statement cover both the case where $p_2,p_3$ are on the same side of $p_1p_4$ (equal angles) and the case where they are on opposite sides (supplementary angles), with no case analysis on the configuration.
--
--   **Formalization note.** Mathlib's `EuclideanGeometry.cospherical_of_two_zsmul_oangle_eq_of_not_collinear`. `∡ a b c` is the oriented angle at $b$, valued in $\mathbb R/2\pi\mathbb Z$. The plane is a two-dimensional real inner product space with a chosen orientation. `Cospherical` means that the points lie on a common sphere, which in the plane is a circle.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `EuclideanGeometry.cospherical_of_two_zsmul_oangle_eq_of_not_collinear`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open EuclideanGeometry

theorem inscribed_angle_converse_concyclic_7a {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)] {p₁ p₂ p₃ p₄ : P}
    (h : (2 : ℤ) • ∡ p₁ p₂ p₄ = (2 : ℤ) • ∡ p₁ p₃ p₄) (hn : ¬Collinear ℝ ({p₁, p₂, p₄} : Set P)) :
    Cospherical ({p₁, p₂, p₃, p₄} : Set P) := by sorry

end FamousTheorems
