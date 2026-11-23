-- Prove2me | Theorems.Thm_Formalism_UG_P_afsplit_decomp
-- name    : Formalism.UG.P.afsplit_decomp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:11.718867+00:00
-- url     : https://prove2.me/theorems/073ed86f-2500-48b5-bad4-07666d3e79d3
-- title:
--   P: afsplit decomp
-- statement:
--   The P construction uses the afsplit decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AfsplitB.lean#L59-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AfsplitB.lean#L59-L68

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitB
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
variable {F : Type} [Field F] [NumberField F] {E : Type} [CommRing E] [Algebra F E]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

theorem Formalism.UG.P.afsplit_decomp (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] 𝔸) :
    afsplitIE v (prV (E := E) v x) = afsplitEps E v * x := by sorry
