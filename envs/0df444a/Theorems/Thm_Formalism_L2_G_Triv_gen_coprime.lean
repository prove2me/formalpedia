-- Prove2me | Theorems.Thm_Formalism_L2_G_Triv_gen_coprime
-- name    : Formalism.L2.G.Triv.gen_coprime
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:37:18.303628+00:00
-- url     : https://prove2.me/theorems/22c721b8-ce65-4825-b1d7-519f0cf8b95b
-- title:
--   Triv: gen coprime
-- statement:
--   The Triv construction uses the gen coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/TrivialTransfer/GenCoprime.lean#L15-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/TrivialTransfer/GenCoprime.lean#L15-L55

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

theorem Formalism.L2.G.Triv.gen_coprime (U : Subgroup (GL (Fin k) 𝒜)) (g : ℕ) (hg : g.Prime) (v : HeightOneSpectrum (𝓞 F))
    (hv : (g : 𝓞 F) ∈ v.asIdeal) (ρ : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F)
    (h : GL (Fin k) (v.adicCompletion F))
    (hU : ∀ z ∈ U, h⁻¹ * bc ρ (bc (prV (E := E) v) z) * h ∈ iwU F k v)
    (x : GL (Fin k) 𝒜) (γ : GL (Fin k) E) (hγ : x⁻¹ * bc (inclE (F := F) 𝔸) γ * x ∈ U) (N : ℕ) (hN : Nat.Coprime N g)
    (hγN : bc (inclE (F := F) 𝔸) γ ^ N = 1) : γ = 1 := by sorry
