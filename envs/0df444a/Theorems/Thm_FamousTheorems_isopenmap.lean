-- Prove2me | Theorems.Thm_FamousTheorems_isopenmap
-- name    : FamousTheorems.isopenmap
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:01:59.537726+00:00
-- url     : https://prove2.me/theorems/edbf6070-5f96-42ca-b683-17396e11d2f8
-- title:
--   The open mapping theorem (functional analysis)
-- statement:
--   **The open mapping theorem.** A surjective continuous linear map between Banach spaces is open. Surjectivity alone forces the map to send open sets to open sets — a purely topological conclusion from an algebraic hypothesis, made possible by completeness via the Baire category theorem. The immediate corollary is the bounded inverse theorem: a continuous linear bijection between Banach spaces has continuous inverse, so there is no such thing as a discontinuous inverse in this setting. The closed graph theorem follows too. Completeness of both spaces is essential; the theorem fails for incomplete normed spaces. **Formalization note.** The map is a `ContinuousLinearMap` and the hypothesis is surjectivity, with both spaces complete. The result is Mathlib's `ContinuousLinearMap.isOpenMap`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem isopenmap :
    ∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : NontriviallyNormedField 𝕜] 
    [inst_1 : NontriviallyNormedField 𝕜'] {σ : 𝕜 →+* 𝕜'} {E : Type u_3} [inst_2 : NormedAddCommGroup E] 
    [inst_3 : NormedSpace 𝕜 E] {F : Type u_4} [inst_4 : NormedAddCommGroup F] [inst_5 : NormedSpace 𝕜' F] (f : E →SL[σ] F) 
    {σ' : 𝕜' →+* 𝕜} [RingHomInvPair σ σ'] [RingHomIsometric σ] [RingHomIsometric σ'] [CompleteSpace F] [CompleteSpace E], 
    Function.Surjective ⇑f → IsOpenMap ⇑f := by sorry

end FamousTheorems
