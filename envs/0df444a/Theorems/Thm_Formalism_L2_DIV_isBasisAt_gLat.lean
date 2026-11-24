-- Prove2me | Theorems.Thm_Formalism_L2_DIV_isBasisAt_gLat
-- name    : Formalism.L2.DIV.isBasisAt_gLat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:16.373622+00:00
-- url     : https://prove2.me/theorems/1638102a-edb1-4bc7-a609-2aaad50fcff5
-- title:
--   DIV: is Basis At g Lat
-- statement:
--   The DIV construction uses the is Basis At g Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L588-L592
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L588-L592

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

theorem Formalism.L2.DIV.isBasisAt_gLat (w : HeightOneSpectrum (𝓞 K)) (g B : GL (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K)) :
    IsBasisAt w (gLat g M) (g * B) ↔ IsBasisAt w M B := by sorry
