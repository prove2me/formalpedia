-- Prove2me | Theorems.Thm_Formalism_UG_P_levelaf_mem_range_of_integral
-- name    : Formalism.UG.P.levelaf_mem_range_of_integral
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:15:57.902264+00:00
-- url     : https://prove2.me/theorems/a79df0a9-8050-42f9-bc40-e2e6e74404d0
-- title:
--   P: levelaf mem range of integral
-- statement:
--   The P construction uses the levelaf mem range of integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelaf.lean#L311-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelaf.lean#L311-L326

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero TensorProduct
variable {L : Type} [CommRing L] {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.levelaf_mem_range_of_integral (O : Subring L) (U : GL n L)
    (h1 : (U : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range)
    (h2 : ((U⁻¹ : GL n L) : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range) :
    U ∈ (bc (n := n) O.subtype).range := by sorry
