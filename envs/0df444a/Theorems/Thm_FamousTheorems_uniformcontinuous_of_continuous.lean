-- Prove2me | Theorems.Thm_FamousTheorems_uniformcontinuous_of_continuous
-- name    : FamousTheorems.uniformcontinuous_of_continuous
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:01:42.614147+00:00
-- url     : https://prove2.me/theorems/9eb4008c-8d0d-4731-8f54-f6d1803ca1a1
-- title:
--   The Heine–Cantor theorem
-- statement:
--   **The Heine\u2013Cantor theorem.** A continuous function on a compact space is uniformly continuous. Pointwise continuity gives a $\delta$ depending on the point; compactness lets finitely many such neighbourhoods cover the space, and the minimum of the corresponding $\delta$'s works everywhere at once. The upgrade fails without compactness — $x \mapsto x^2$ on $\mathbb{R}$ and $x \mapsto 1/x$ on $(0,1)$ are continuous but not uniformly so. Uniform continuity is what makes Riemann integration of continuous functions work and what allows continuous functions to be approximated by step functions with a single modulus. **Formalization note.** The statement is for uniform spaces, of which metric spaces are a special case. The result is Mathlib's `CompactSpace.uniformContinuous_of_continuous`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem uniformcontinuous_of_continuous :
    ∀ {α : Type u_1} {β : Type u_2} [inst : UniformSpace α] 
    [inst_1 : UniformSpace β] [CompactSpace α] {f : α → β}, Continuous f → UniformContinuous f := by sorry

end FamousTheorems
