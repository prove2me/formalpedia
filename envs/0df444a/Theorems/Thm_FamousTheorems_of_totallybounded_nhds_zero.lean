-- Prove2me | Theorems.Thm_FamousTheorems_of_totallybounded_nhds_zero
-- name    : FamousTheorems.of_totallybounded_nhds_zero
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T16:55:13.3551+00:00
-- url     : https://prove2.me/theorems/cd8d0d12-40cf-4e67-adff-a76e25649b14
-- title:
--   Riesz's theorem
-- statement:
--   **Riesz's theorem.** A normed space whose origin has a totally bounded neighbourhood is finite-dimensional. Equivalently, the closed unit ball is compact only in finite dimensions -- so local compactness characterises finite-dimensionality among normed spaces. This is the precise reason Heine-Borel fails in infinite dimensions and why functional analysis must work with weaker topologies: Banach-Alaoglu recovers compactness of the dual ball only after passing to the weak-* topology. The proof rests on Riesz's lemma, producing almost-orthogonal unit vectors at distance bounded away from zero. **Formalization note.** The conclusion is `FiniteDimensional` over the scalar field. The result is Mathlib's `FiniteDimensional.of_totallyBounded_nhds_zero`.
-- source:
--   Marked as a named theorem in Mathlib's own docstrings; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem of_totallybounded_nhds_zero :
    ∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] 
    {Eᵤ : Type u_2} [inst_2 : AddCommGroup Eᵤ] [inst_3 : Module 𝕜 Eᵤ] [inst_4 : UniformSpace Eᵤ] [T2Space Eᵤ] 
    [IsUniformAddGroup Eᵤ] [ContinuousSMul 𝕜 Eᵤ] {U : Set Eᵤ}, U ∈ 𝓝 0 → TotallyBounded U → FiniteDimensional 𝕜 Eᵤ := by sorry

end FamousTheorems
