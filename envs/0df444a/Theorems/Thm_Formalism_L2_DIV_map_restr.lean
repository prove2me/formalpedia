-- Prove2me | Theorems.Thm_Formalism_L2_DIV_map_restr
-- name    : Formalism.L2.DIV.map_restr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:09:19.323587+00:00
-- url     : https://prove2.me/theorems/44fcc717-9077-4087-963c-3068022f04fb
-- title:
--   DIV: map restr
-- statement:
--   The DIV construction uses the map restr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/FramesLemmas.lean#L147-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/FramesLemmas.lean#L147-L151

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Frames
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_FramesLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder MatrixOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues

theorem Formalism.L2.DIV.map_restr {K : Type} [Field K] [StarRing K] (σ : K →+* ℂ) {n d : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (E : Matrix (Fin n) (Fin d) K)
    (hE : ∀ i a, σ (star (E i a)) = starRingEnd ℂ (σ (E i a))) :
    (Eᴴ * H * E).map σ = restrMetC (E.map σ) (H.map σ) := by sorry
