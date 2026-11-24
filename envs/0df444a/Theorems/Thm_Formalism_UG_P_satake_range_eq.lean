-- Prove2me | Theorems.Thm_Formalism_UG_P_satake_range_eq
-- name    : Formalism.UG.P.satake_range_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:34:52.029841+00:00
-- url     : https://prove2.me/theorems/5b72f602-5489-4a79-be64-c23e91e13170
-- title:
--   P: satake range eq
-- statement:
--   The P construction uses the satake range eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Satake.lean#L163-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Satake.lean#L163-L179

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeRes
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Satake
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
  {ϖ : v.adicCompletion F} (hϖ : ϖ ∈ Ov F v) (hu : IsUnifV F v ϖ)

theorem Formalism.UG.P.satake_range_eq [Fintype (satakeRes (Ov F v) ⟨ϖ, hϖ⟩)] (hTjCosets : TjCosets) {j : ℕ}
    (hj : j ≤ n) :
    Set.range (fun i : SatakeIdx v hϖ (n := n) j =>
      ((satakeB v hϖ hu i : GL (Fin n) (v.adicCompletion F)) :
        GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v))) =
    {x : GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v) | x.out ∈ satakeTset v ϖ j} := by sorry
