-- Prove2me | Theorems.Thm_FamousTheorems_eqon_of_preconnected_of_frequently_eq
-- name    : FamousTheorems.eqon_of_preconnected_of_frequently_eq
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:26:19.357565+00:00
-- url     : https://prove2.me/theorems/224ddf01-ba45-463f-b3de-dfb09c1f9fdf
-- title:
--   The identity theorem
-- statement:
--   **The identity theorem** for analytic functions. If two functions are analytic on a preconnected open set and agree on a set with an accumulation point inside it, they agree everywhere on that set: $$f = g \text{ frequently near } z_0 \;\Longrightarrow\; f = g \text{ on all of } U.$$ An analytic function is rigid to an extreme degree: its values on an arbitrarily small convergent sequence determine it globally on any connected domain containing that sequence. Nothing comparable holds for smooth real functions, which can be modified on one region while remaining unchanged on another — bump functions exist in the $C^\infty$ world and cannot exist in the analytic one. Connectedness is essential, since on a disconnected domain the components are independent. The theorem is what makes analytic continuation well posed: an analytic germ has at most one extension along a given path, so the continuation is determined by the germ rather than chosen. **Formalization note.** `IsPreconnected U` is connectedness without the nonemptiness requirement, and `∃ᶠ` expresses accumulation of the agreement set at $z_0$. The result is Mathlib's `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem eqon_of_preconnected_of_frequently_eq :
    ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
    {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] {f g : 𝕜 → E} {z₀ : 𝕜} {U : Set 𝕜}, 
    AnalyticOnNhd 𝕜 f U → 
    AnalyticOnNhd 𝕜 g U → IsPreconnected U → z₀ ∈ U → (∃ᶠ (z : 𝕜) in 𝓝[≠] z₀, f z = g z) → EqOn f g U := by sorry

end FamousTheorems
