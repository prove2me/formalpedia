-- Prove2me | Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_smul_mem_cut
-- name    : Formalism.IndefR.LatticeTransfer.Lat.smul_mem_cut
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:13.422142+00:00
-- url     : https://prove2.me/theorems/32331718-7ac5-46c6-b1df-b0008332a7b8
-- title:
--   Lat: smul mem cut
-- statement:
--   The Lat construction uses the smul mem cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/MemSpanOfSmulMem.lean#L187-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/MemSpanOfSmulMem.lean#L187-L194

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

theorem Formalism.IndefR.LatticeTransfer.Lat.smul_mem_cut (hP : IdemP) (ρ : Representation K G V) {A : Submodule (𝓞 K) V}
    (hA : ∀ g : G, ∀ a ∈ A, ρ g a ∈ A) (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) (g : G)
    {p : V →ₗ[K] V} (hp : ∀ a, p (p a) = p a) {a : V} (ha : a ∈ A)
    (hx : p ((epP H χ ρ ∘ₗ ρ g) a) = (epP H χ ρ ∘ₗ ρ g) a) :
    (Fintype.card G : 𝓞 K) • (epP H χ ρ ∘ₗ ρ g) a ∈ cut A p := by sorry
