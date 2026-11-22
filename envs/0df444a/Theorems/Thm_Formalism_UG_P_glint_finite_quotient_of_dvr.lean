-- Prove2me | Theorems.Thm_Formalism_UG_P_glint_finite_quotient_of_dvr
-- name    : Formalism.UG.P.glint_finite_quotient_of_dvr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:25:36.165811+00:00
-- url     : https://prove2.me/theorems/c2a6d62e-d23e-4fb9-b5a3-6c72cccddc46
-- title:
--   P: glint finite quotient of dvr
-- statement:
--   The P construction uses the glint finite quotient of dvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/GlintPrincRelIndexNeZero.lean#L190-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/GlintPrincRelIndexNeZero.lean#L190-L215

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

theorem Formalism.UG.P.glint_finite_quotient_of_dvr {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (h : Finite (IsLocalRing.ResidueField R)) (I : Ideal R) (hI : I ≠ ⊥) : Finite (R ⧸ I) := by sorry
