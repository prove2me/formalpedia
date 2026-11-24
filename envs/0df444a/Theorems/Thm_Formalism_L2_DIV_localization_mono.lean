-- Prove2me | Theorems.Thm_Formalism_L2_DIV_localization_mono
-- name    : Formalism.L2.DIV.localization_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:28.690546+00:00
-- url     : https://prove2.me/theorems/d8988162-f262-49cb-98c1-710b7ab87201
-- title:
--   DIV: localization mono
-- statement:
--   The DIV construction uses the localization mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L243-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L243-L246

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

theorem Formalism.L2.DIV.localization_mono {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime]
    {L L' : Submodule R W} (h : L ≤ L') : Formalism.HermitianLatticesTheory.localization₂ p L ≤ Formalism.HermitianLatticesTheory.localization₂ p L' := by sorry
