-- Prove2me | Theorems.Thm_Formalism_UG_P_transport_bc_mem
-- name    : Formalism.UG.P.transport_bc_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:23.278152+00:00
-- url     : https://prove2.me/theorems/4aa32dc4-a187-4b79-858d-5f0ddf3e3318
-- title:
--   P: transport bc mem
-- statement:
--   The P construction uses the transport bc mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Transport.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Transport.lean#L18-L23

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Transport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG

theorem Formalism.UG.P.transport_bc_mem {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n]
    [DecidableEq n] (σ : A →+* A) (σ' : B →+* B) (φ : A →+* B) (h : φ.comp σ = σ'.comp φ)
    (J : Matrix n n A) (g : GL n A) (hg : g ∈ UJ σ J) : bc φ g ∈ UJ σ' (J.map φ) := by sorry
