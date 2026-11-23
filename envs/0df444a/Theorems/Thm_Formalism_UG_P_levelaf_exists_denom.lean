-- Prove2me | Theorems.Thm_Formalism_UG_P_levelaf_exists_denom
-- name    : Formalism.UG.P.levelaf_exists_denom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:31:22.950997+00:00
-- url     : https://prove2.me/theorems/949a8e40-7e10-4af4-a3a6-2918bfa9048a
-- title:
--   P: levelaf exists denom
-- statement:
--   The P construction uses the levelaf exists denom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelaf.lean#L423-L442
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelaf.lean#L423-L442

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

theorem Formalism.UG.P.levelaf_exists_denom (g : GL n 𝒜) : ∃ d : 𝓞 F, d ≠ 0 ∧ ∃ c : 𝒮, (c : 𝒜) = levelafC E d ∧
    (c : 𝒜) • (g : Matrix n n 𝒜) ∈ (RingHom.mapMatrix (m := n) (𝒮).subtype).range ∧
    (c : 𝒜) • ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) ∈ (RingHom.mapMatrix (m := n) (𝒮).subtype).range := by sorry
