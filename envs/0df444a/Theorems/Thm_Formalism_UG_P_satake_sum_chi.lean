-- Prove2me | Theorems.Thm_Formalism_UG_P_satake_sum_chi
-- name    : Formalism.UG.P.satake_sum_chi
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:34:22.074059+00:00
-- url     : https://prove2.me/theorems/a4acde05-419e-44ee-b15e-d9524ae0d419
-- title:
--   P: satake sum chi
-- statement:
--   The P construction uses the satake sum chi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Satake.lean#L232-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Satake.lean#L232-L245

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

theorem Formalism.UG.P.satake_sum_chi [Fintype (satakeRes (Ov F v) ⟨ϖ, hϖ⟩)] (α : Fin n → ℂ) (j : ℕ) :
    ∑ i : SatakeIdx v hϖ (n := n) j, chiDelta F v α (satakeB v hϖ hu i) =
      (qV F v : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2) * Multiset.esymm (Multiset.map α Finset.univ.val) j := by sorry
