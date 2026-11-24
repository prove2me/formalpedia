-- Prove2me | Theorems.Thm_Formalism_UG_P_adelstab_core
-- name    : Formalism.UG.P.adelstab_core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:10:58.951013+00:00
-- url     : https://prove2.me/theorems/00683374-8318-495b-b5b6-18d2c260eedf
-- title:
--   P: adelstab core
-- statement:
--   The P construction uses the adelstab core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Adelstab.lean#L254-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Adelstab.lean#L254-L293

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabfin
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Adelstab
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem Formalism.UG.P.adelstab_core (σ : E →ₐ[F] E) (J : Matrix n n E)
    (hτ : ∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ)
    (hH : IsHerm (σ : E →+* E) J) (hdet : IsUnit J.det) (hdef : IsTotDef σ J)
    (L : Submodule 𝒮 (n → 𝒜)) (K : Subgroup (GL n 𝒜)) (hK : K ≤ stabGL L) (c₁ c₂ : 𝓞 F)
    (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0)
    (hL₁ : ∀ v : n → 𝒜, (∀ i, v i ∈ 𝒮) → (fun i => levelafC E c₁ * v i) ∈ L)
    (hL₂ : ∀ v ∈ L, ∀ i, levelafC E c₂ * v i ∈ 𝒮)
    (g : UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    Finite (stabAt ((ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf
      (UPts σ J (FiniteAdeleRing (𝓞 F) F))) (K.subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))) g) := by sorry
