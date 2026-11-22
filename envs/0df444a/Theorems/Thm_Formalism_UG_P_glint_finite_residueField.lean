-- Prove2me | Theorems.Thm_Formalism_UG_P_glint_finite_residueField
-- name    : Formalism.UG.P.glint_finite_residueField
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:26:01.884231+00:00
-- url     : https://prove2.me/theorems/e87989fd-06f9-4aec-9c01-383fe1e28f3c
-- title:
--   P: glint finite residue Field
-- statement:
--   The P construction uses the glint finite residue Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/GlintPrincRelIndexNeZero.lean#L155-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/GlintPrincRelIndexNeZero.lean#L155-L188

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Lemmata_NearbyExistence_ExistsNear
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem Formalism.UG.P.glint_finite_residueField :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := by sorry
