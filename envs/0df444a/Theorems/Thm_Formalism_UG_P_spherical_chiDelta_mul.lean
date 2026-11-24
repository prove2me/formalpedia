-- Prove2me | Theorems.Thm_Formalism_UG_P_spherical_chiDelta_mul
-- name    : Formalism.UG.P.spherical_chiDelta_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:59.695971+00:00
-- url     : https://prove2.me/theorems/9ee90cee-4485-4a62-9c67-65ff6edbb8ba
-- title:
--   P: spherical chi Delta mul
-- statement:
--   The P construction uses the spherical chi Delta mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SphericalA.lean#L79-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/SphericalA.lean#L79-L96

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SphericalA
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

theorem Formalism.UG.P.spherical_chiDelta_mul {n : ℕ} (α : Fin n → ℂ) (hα : ∀ i, α i ≠ 0) (b c : GL (Fin n) (v.adicCompletion F))
    (hb : (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id)
    (hc : (c : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id) :
    chiDelta F v α (b * c) = chiDelta F v α b * chiDelta F v α c := by sorry
