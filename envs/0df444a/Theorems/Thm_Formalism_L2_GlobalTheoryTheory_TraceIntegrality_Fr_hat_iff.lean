-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_TraceIntegrality_Fr_hat_iff
-- name    : Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr.hat_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:48:04.343977+00:00
-- url     : https://prove2.me/theorems/c4a01fe3-8767-46db-85e2-ceaa82de6b3a
-- title:
--   Fr: hat iff
-- statement:
--   The Fr construction uses the hat iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL4/PFrCore.lean#L105-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL4/PFrCore.lean#L105-L117

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL4_PFrCore
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
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.TraceIntegrality Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr
open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions Formalism.L2.GlobalTheoryTheory.Comp
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr.hat_iff (G : GL n E) {Λ Λ' : Submodule (𝓞 E) (n → E)} (h : ∀ x, x ∈ Λ ↔ (G : Matrix n n E) *ᵥ x ∈ Λ')
    (u : n → 𝒜) : u ∈ hat F Λ ↔ ((G : Matrix n n E).map ιA) *ᵥ u ∈ hat F Λ' := by sorry
