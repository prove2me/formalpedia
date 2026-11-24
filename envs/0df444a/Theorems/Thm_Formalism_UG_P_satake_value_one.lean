-- Prove2me | Theorems.Thm_Formalism_UG_P_satake_value_one
-- name    : Formalism.UG.P.satake_value_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:34:48.199269+00:00
-- url     : https://prove2.me/theorems/4469b858-ad0c-424a-81a2-26cc9a7ffde3
-- title:
--   P: satake value one
-- statement:
--   The P construction uses the satake value one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Satake.lean#L247-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Satake.lean#L247-L276

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

theorem Formalism.UG.P.satake_value_one [Fintype (satakeRes (Ov F v) ⟨ϖ, hϖ⟩)] (hTjCosets : TjCosets) {j : ℕ}
    (hj : j ≤ n) (α : Fin n → ℂ) (φ : GL (Fin n) (v.adicCompletion F) → ℂ)
    (hφ : IsSpherical F v α φ) :
    hAct (GLint (Fin n) (Ov F v)) (Tj ℂ n (Ov F v) ϖ j) φ 1 =
      (∑ i : SatakeIdx v hϖ (n := n) j, chiDelta F v α (satakeB v hϖ hu i)) * φ 1 := by sorry
