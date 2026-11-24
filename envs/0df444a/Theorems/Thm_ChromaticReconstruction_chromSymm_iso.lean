-- Prove2me | Theorems.Thm_ChromaticReconstruction_chromSymm_iso
-- name    : ChromaticReconstruction.chromSymm_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:57:54.428092+00:00
-- url     : https://prove2.me/theorems/68dcd9ac-8e5a-49cd-b61e-a204fd5fb67b
-- title:
--   Chromatic Reconstruction: chrom Symm iso
-- statement:
--   The chromatic symmetric function is an isomorphism invariant.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Components.lean#L196-L220
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Components.lean#L196-L220

import Definitions.Def_RequestProject_Defs
import Definitions.Def_RequestProject_Components
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*}
variable [Fintype V] [Fintype W]

theorem ChromaticReconstruction.chromSymm_iso {G : SimpleGraph V} {G' : SimpleGraph W} (e : G ≃g G') :
    chromSymm G = chromSymm G' := by sorry
