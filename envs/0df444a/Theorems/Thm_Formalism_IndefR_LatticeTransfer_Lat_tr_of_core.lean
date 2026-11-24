-- Prove2me | Theorems.Thm_Formalism_IndefR_LatticeTransfer_Lat_tr_of_core
-- name    : Formalism.IndefR.LatticeTransfer.Lat.tr_of_core
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:23.543818+00:00
-- url     : https://prove2.me/theorems/3836160a-f278-45f9-af43-f1ebc87e2fd8
-- title:
--   Lat: tr of core
-- statement:
--   The Lat construction uses the tr of core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/MemSpanOfSmulMem.lean#L162-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/MemSpanOfSmulMem.lean#L162-L185

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

theorem Formalism.IndefR.LatticeTransfer.Lat.tr_of_core (hP : IdemP) {T : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]
    {τ : Representation K G T} {H₀ : Subgroup G} {χ₀ : H₀ →* (𝓞 K)ˣ} {H : Subgroup G}
    {χ : H →* (𝓞 K)ˣ} {n : ℕ} {γ δ : Fin n → G} {c : Matrix (Fin n) (Fin n) K}
    {Γ : Matrix (Fin n) (Fin n) (𝓞 K)} (h : CoreData τ H₀ χ₀ H χ γ δ c Γ)
    (ρ : Representation K G V) (he : eS τ ρ ∘ₗ eS τ ρ = eS τ ρ) :
    Tr (epP H₀ χ₀ ρ ∘ₗ eS τ ρ) (epP H χ ρ ∘ₗ eS τ ρ) (fun j => epP H χ ρ ∘ₗ ρ (γ j))
      (fun i => epP H₀ χ₀ ρ ∘ₗ ρ (δ i)) c := by sorry
