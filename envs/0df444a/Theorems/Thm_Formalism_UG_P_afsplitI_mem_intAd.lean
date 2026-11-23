-- Prove2me | Theorems.Thm_Formalism_UG_P_afsplitI_mem_intAd
-- name    : Formalism.UG.P.afsplitI_mem_intAd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:48:58.175683+00:00
-- url     : https://prove2.me/theorems/4527633a-f145-4878-bd2d-929edfa6df86
-- title:
--   P: afsplit I mem int Ad
-- statement:
--   The P construction uses the afsplit I mem int Ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AfsplitA.lean#L75-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/AfsplitA.lean#L75-L80

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitA
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
variable {F : Type} [Field F] [NumberField F]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F

theorem Formalism.UG.P.afsplitI_mem_intAd (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F)
    (hx : x ∈ v.adicCompletionIntegers F) : afsplitI v x ∈ intAd F := by sorry
