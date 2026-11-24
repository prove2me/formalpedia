-- Prove2me | Theorems.Thm_Formalism_UG_P_spherical_iwasawa
-- name    : Formalism.UG.P.spherical_iwasawa
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:36:50.31806+00:00
-- url     : https://prove2.me/theorems/9b054015-0de6-4022-bc6e-d806c141e2bb
-- title:
--   P: spherical iwasawa
-- statement:
--   The P construction uses the spherical iwasawa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Spherical.lean#L163-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Spherical.lean#L163-L192

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SphericalA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Spherical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.UG
open Formalism Formalism.UG Formalism.UG.P
variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem Formalism.UG.P.spherical_iwasawa {n : ℕ} (g : GL (Fin n) (v.adicCompletion F)) :
    ∃ b k : GL (Fin n) (v.adicCompletion F),
      (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id ∧
      k ∈ GLint (Fin n) (Ov F v) ∧ g = b * k := by sorry
