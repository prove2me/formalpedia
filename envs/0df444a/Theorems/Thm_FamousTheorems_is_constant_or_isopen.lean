-- Prove2me | Theorems.Thm_FamousTheorems_is_constant_or_isopen
-- name    : FamousTheorems.is_constant_or_isopen
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:01:54.34512+00:00
-- url     : https://prove2.me/theorems/1b8cc3a4-3d68-4caf-90c1-8c227a78fb6b
-- title:
--   The open mapping theorem (complex analysis)
-- statement:
--   **The open mapping theorem for analytic functions.** A function analytic on a preconnected open set is either constant or an open map. There is no middle ground: a nonconstant analytic function cannot compress any open set into something with empty interior. This is a rigidity with no real-variable analogue — $x \mapsto x^2$ on $\mathbb{R}$ is nonconstant and not open. The maximum modulus principle is an immediate corollary, since an interior maximum of $|f|$ would force a neighbourhood of $f(z_0)$ into the closed disc of that radius, contradicting openness. **Formalization note.** `AnalyticOnNhd` is analyticity on a neighbourhood of each point of the set, and `IsPreconnected` is connectedness without nonemptiness. The result is Mathlib's `AnalyticOnNhd.is_constant_or_isOpen`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem is_constant_or_isopen :
    ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] 
    {U : Set E} {g : E → ℂ}, 
    AnalyticOnNhd ℂ g U → IsPreconnected U → (∃ w, ∀ z ∈ U, g z = w) ∨ ∀ s ⊆ U, IsOpen s → IsOpen (g '' s) := by sorry

end FamousTheorems
