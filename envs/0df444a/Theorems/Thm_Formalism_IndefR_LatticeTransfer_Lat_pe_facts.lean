-- Prove2me | Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_pe_facts
-- name    : Formalism.IndefR.LatticeTransfer.Lat.pe_facts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:41.197963+00:00
-- url     : https://prove2.me/theorems/841e6ea6-b775-4f9d-9ece-b72f71cf580f
-- title:
--   Lat: pe facts
-- statement:
--   The Lat construction uses the pe facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/MemSpanOfSmulMem.lean#L148-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/MemSpanOfSmulMem.lean#L148-L160

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_MemSpanOfSmulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer Formalism.IndefR.LatticeTransfer.Lat
open Formalism.IndefR.TransferLatticeStatement Formalism.HN Formalism.IndefR.LatticeTransfer
variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.IndefR.LatticeTransfer.Lat.pe_facts {ε e : V →ₗ[K] V} (hε : ε ∘ₗ ε = ε) (he : e ∘ₗ e = e) (hc : e ∘ₗ ε = ε ∘ₗ e) :
    (∀ a, (ε ∘ₗ e) ((ε ∘ₗ e) a) = (ε ∘ₗ e) a) ∧
    ∀ a, (ε ∘ₗ e) a = a ↔ ε a = a ∧ e a = a := by sorry
