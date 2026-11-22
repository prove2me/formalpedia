-- Prove2me | Theorems.Thm_Formalism_UG_P_adelstab_dual
-- name    : Formalism.UG.P.adelstab_dual
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:59:05.22885+00:00
-- url     : https://prove2.me/theorems/87fae986-027e-485a-ba54-a25d3bb16ea0
-- title:
--   P: adelstab dual
-- statement:
--   The P construction uses the adelstab dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Adelstab.lean#L61-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Adelstab.lean#L61-L74

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
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

theorem Formalism.UG.P.adelstab_dual {ι : Type} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι F E) (d : E)
    (hd : ∀ i, IsIntegral ℤ (d * β i)) (e : E)
    (he : ∀ b : 𝓞 E, Algebra.trace F E (e * algebraMap (𝓞 E) E b) ∈ (algebraMap (𝓞 F) F).range) :
    d * e ∈ Submodule.span (𝓞 F)
      (Set.range ((Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) β)) := by sorry
