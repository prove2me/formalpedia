-- Prove2me | Theorems.Thm_Formalism_L2_DIV_quot_eq_restr_of
-- name    : Formalism.L2.DIV.quot_eq_restr_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:10:13.022199+00:00
-- url     : https://prove2.me/theorems/ef55fd95-06ee-44e1-8c42-580a844313f7
-- title:
--   DIV: quot eq restr of
-- statement:
--   The DIV construction uses the quot eq restr of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/FramesLemmas.lean#L174-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/FramesLemmas.lean#L174-L188

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

theorem Formalism.L2.DIV.quot_eq_restr_of {K : Type} [Field K] [NumberField K] [StarRing K] (v : InfinitePlace K)
    {n d : ℕ} (H : Matrix (Fin n) (Fin n) K) (hH : (H.map v.embedding).PosDef)
    (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K)
    (hE : ∀ i a, v.embedding (star (E i a)) = starRingEnd ℂ (v.embedding (E i a)))
    (hP : IsOrthProj H E Pr) : quotFrame Pr H v = restrFrame E H v := by sorry
