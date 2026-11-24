-- Prove2me | Theorems.Thm_Formalism_L2_DIV_localization_gLat
-- name    : Formalism.L2.DIV.localization_gLat
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:42.254942+00:00
-- url     : https://prove2.me/theorems/0cb7e091-5fd2-4ff6-9784-15b25a7c3b61
-- title:
--   DIV: localization g Lat
-- statement:
--   The DIV construction uses the localization g Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L561-L579
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L561-L579

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

theorem Formalism.L2.DIV.localization_gLat (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K)) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (gLat g M) = gLat g (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M) := by sorry
