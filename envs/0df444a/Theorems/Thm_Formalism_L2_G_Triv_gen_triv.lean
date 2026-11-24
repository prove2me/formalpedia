-- Prove2me | Theorems.Thm_Formalism_L2_G_Triv_gen_triv
-- name    : Formalism.L2.G.Triv.gen_triv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:37:11.845501+00:00
-- url     : https://prove2.me/theorems/4f687017-ad04-4780-8265-d0763daa4726
-- title:
--   Triv: gen triv
-- statement:
--   The Triv construction uses the gen triv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/TrivialTransfer/GenCoprime.lean#L63-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/TrivialTransfer/GenCoprime.lean#L63-L124

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_OneAddPowOfSq
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_FiniteStabAtOfLocal
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_GenCoprime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P Formalism.BasicNotions
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Triv
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ}
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F

theorem Formalism.L2.G.Triv.gen_triv (σ : E →ₐ[F] E) (J : Matrix (Fin k) (Fin k) E)
    (hτ : ∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ)
    (hH : IsHerm (σ : E →+* E) J) (hdet : IsUnit J.det) (hdef : IsTotDef σ J)
    (Λ : Submodule (𝓞 E) (Fin k → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (Fin k → E)) = ⊤)
    (U : Subgroup (GL (Fin k) 𝒜))
    (hU : ∀ x ∈ U, ∀ v : HeightOneSpectrum (𝓞 F),
      bc (prV (E := E) v) x ∈ stabGL (latS (F := F) (v.adicCompletion F) (SV E v) Λ))
    (g : Fin 2 → ℕ) (hg : ∀ i, (g i).Prime) (hne : g 0 ≠ g 1) (v : Fin 2 → HeightOneSpectrum (𝓞 F))
    (hv : ∀ i, (g i : 𝓞 F) ∈ (v i).asIdeal) (ρ : ∀ i, E ⊗[F] (v i).adicCompletion F →+* (v i).adicCompletion F)
    (h : ∀ i, GL (Fin k) ((v i).adicCompletion F))
    (hUg : ∀ i, ∀ z ∈ U, (h i)⁻¹ * bc (ρ i) (bc (prV (E := E) (v i)) z) * h i ∈ iwU F k (v i))
    (x : UPts σ J 𝔸) (γ : GL (Fin k) E) (hγJ : γ ∈ UJ (σ : E →+* E) J)
    (hγ : (x : GL (Fin k) 𝒜)⁻¹ * bc (inclE (F := F) 𝔸) γ * x ∈ U) : γ = 1 := by sorry
