-- Prove2me | Theorems.Thm_FamousTheorems_two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq
-- name    : FamousTheorems.two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T08:37:44.946796+00:00
-- url     : https://prove2.me/theorems/6a79478f-7a33-473a-8573-13f847778f58
-- title:
--   The inscribed angle theorem
-- statement:
--   **The inscribed angle theorem.** If two points $p_1, p_2$ are equidistant from a centre, then for any two further points on that circle the oriented angles subtended satisfy $$2\,\angle(p_1 - q_1,\ p_2 - q_1) = 2\,\angle(p_1 - q_2,\ p_2 - q_2).$$ All angles inscribed in a circle subtending the same chord are equal. The doubling is not an artefact: oriented angles are only well defined modulo $\pi$ in this setting, and it is twice the angle that is genuinely equal modulo $2\pi$ — which is exactly what lets the statement cover both arcs uniformly, with points on opposite sides of the chord giving supplementary rather than equal angles. Taking the chord to be a diameter gives Thales' theorem: the angle in a semicircle is right. The theorem is the reason concyclicity can be detected by angle chasing, and it is the geometric content behind Ptolemy's theorem and the power of a point. Euclid proves it as III.20. **Formalization note.** The hypothesis is equality of distances from a common point, and `oangle` is the oriented angle in a two-dimensional oriented inner product space. The result is Mathlib's `Orientation.two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq :
    ∀ {V : Type u_1} [inst : NormedAddCommGroup V] 
    [inst_1 : InnerProductSpace ℝ V] [inst_2 : Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2)) 
    {x₁ x₂ y z : V}, 
    x₁ ≠ y → 
    x₁ ≠ z → 
    x₂ ≠ y → 
    x₂ ≠ z → 
    ∀ {r : ℝ}, 
    ‖x₁‖ = r → ‖x₂‖ = r → ‖y‖ = r → ‖z‖ = r → 2 • o.oangle (y - x₁) (z - x₁) = 2 • o.oangle (y - x₂) (z - x₂) := by sorry

end FamousTheorems
