-- Prove2me | Theorems.Thm_Formalism_L2_DIV_transLat_gLat
-- name    : Formalism.L2.DIV.transLat_gLat
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:21.407671+00:00
-- url     : https://prove2.me/theorems/7555b881-3dc0-47ac-8da8-46ba9ea18397
-- title:
--   DIV: trans Lat g Lat
-- statement:
--   The DIV construction uses the trans Lat g Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L618-L631
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L618-L631

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

theorem Formalism.L2.DIV.transLat_gLat (lam : ι → DomWeight n) (T : Submodule (𝓞 K) (Pol K ι n))
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (g : ι → GL (Fin n) K) :
    transLat lam T (fun τ => gLat (g τ) (M τ)) = (transLat lam T M).map ((actP lam g).restrictScalars (𝓞 K)) := by sorry
