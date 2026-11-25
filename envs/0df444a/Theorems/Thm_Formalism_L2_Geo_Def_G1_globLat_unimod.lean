-- Prove2me | Theorems.Thm_Formalism_L2_Geo_Def_G1_globLat_unimod
-- name    : Formalism.L2.Geo.Def.G1.globLat_unimod
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:49:18.66318+00:00
-- url     : https://prove2.me/theorems/aa501851-849a-4946-a7ec-15c26f616428
-- title:
--   G1: glob Lat unimod
-- statement:
--   The G1 construction uses the glob Lat unimod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/GeometryDefinitions/GlobLatUnimod.lean#L42-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/GeometryDefinitions/GlobLatUnimod.lean#L42-L97

import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_DualFrame
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsScale
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_GlobLatUnimod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Def Formalism.L2.Geo.Def.G1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem Formalism.L2.Geo.Def.G1.globLat_unimod {n : ℕ} (σ : E →ₐ[F] E) (hσ : ∀ x, σ x = star x) (J : Matrix (Fin n) (Fin n) E)
    (hs : (Formalism.DivisionValues.hform J).IsSymm) (hnd : (Formalism.DivisionValues.hform J).Nondegenerate)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsLattice E Λ)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular (Formalism.DivisionValues.hform J) Λ)
    (g : GL (Fin n) 𝒜) (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    Formalism.HermitianLatticesTheory.IsUnimodular (Formalism.DivisionValues.hform J) (Formalism.UG.CS.globLat g Λ) := by sorry
