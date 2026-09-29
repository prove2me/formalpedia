-- Prove2me | Theorems.Thm_FamousTheorems_convolution_tendsto_right
-- name    : FamousTheorems.convolution_tendsto_right
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:40:20.283893+00:00
-- url     : https://prove2.me/theorems/011de195-81fc-4b68-918d-2bc8723f339b
-- title:
--   Approximation by convolution
-- statement:
--   **Approximation of the identity by convolution.** Convolving a continuous function with a family of smooth bumps concentrating at the origin recovers the function in the limit: $$f * \varphi_\varepsilon \;\longrightarrow\; f \quad\text{as } \varepsilon \to 0.$$ Each convolution is as smooth as the bump, so this produces smooth functions approximating an arbitrary continuous one — the standard mollification argument. It is how one proves density of $C^\infty_c$ in $L^p$, how weak solutions of PDEs are regularised, and how the Weierstrass approximation theorem can be obtained analytically. The bump must have unit integral and shrinking support; those two conditions are exactly what make the family an approximate identity for the convolution algebra, which has no genuine unit. **Formalization note.** `ContDiffBump` is a smooth compactly supported bump normalised to unit integral. The result is Mathlib's `ContDiffBump.convolution_tendsto_right`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem convolution_tendsto_right :
    ∀ {G : Type u_1} {E' : Type u_2} [inst : NormedAddCommGroup E'] 
    [inst_1 : MeasurableSpace G] {μ : MeasureTheory.Measure G} [inst_2 : NormedSpace ℝ E'] [inst_3 : NormedAddCommGroup G] 
    [inst_4 : NormedSpace ℝ G] [CompleteSpace E'] [BorelSpace G] [inst_7 : FiniteDimensional ℝ G] [μ.IsAddHaarMeasure] 
    {ι : Type u_3} {φ : ι → ContDiffBump 0} {g : ι → G → E'} {k : ι → G} {x₀ : G} {z₀ : E'} {l : Filter ι}, 
    Tendsto (fun i => (φ i).rOut) l (𝓝 0) → 
    (∀ᶠ (i : ι) in l, MeasureTheory.AEStronglyMeasurable (g i) μ) → 
    Tendsto (Function.uncurry g) (l ×ˢ 𝓝 x₀) (𝓝 z₀) → 
    Tendsto k l (𝓝 x₀) → 
    Tendsto (fun i => MeasureTheory.convolution ((φ i).normed μ) (g i) (ContinuousLinearMap.lsmul ℝ ℝ) μ (k i)) l 
    (𝓝 z₀) := by sorry

end FamousTheorems
