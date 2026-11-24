-- Prove2me | Theorems.Thm_Formalism_L2_Geo_Def_PN_prod_eps_eq
-- name    : Formalism.L2.Geo.Def.PN.prod_eps_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:50:39.865779+00:00
-- url     : https://prove2.me/theorems/0b4b3a2a-bcc7-4a76-8e8d-26a81f7748c3
-- title:
--   PN: prod eps eq
-- statement:
--   The PN construction uses the prod eps eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/GeometryDefinitions/PNeatB.lean#L105-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/GeometryDefinitions/PNeatB.lean#L105-L142

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PNeatB
import Theorems.Thm_Formalism_UG_P_levelaf_finite_places

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Def Formalism.L2.Geo.Def.PN
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

theorem Formalism.L2.Geo.Def.PN.prod_eps_eq (d : 𝓞 F) (hd : d ≠ 0) :
    ∃ a ∈ intAd F, (∏ v ∈ (levelaf_finite_places d hd).toFinset, (1 - afsplitEps E v)) =
      ((1 : E) ⊗ₜ[F] a) * levelafC E d := by sorry
