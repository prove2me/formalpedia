-- Prove2me | Theorems.Thm_Formalism_L2_DIV_embGL_coe
-- name    : Formalism.L2.DIV.embGL_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:00.263054+00:00
-- url     : https://prove2.me/theorems/9eed7395-e37b-4238-b4fe-4e8aabef765a
-- title:
--   DIV: emb GL coe
-- statement:
--   The DIV construction uses the emb GL coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L273-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L273-L274

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

theorem Formalism.L2.DIV.embGL_coe {E K : Type} [Field E] [Field K] {ι : Type} {n : ℕ} (emb : ι → E →+* K) (γ : GL (Fin n) E) (τ : ι) :
    ((embGL emb γ τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (γ : Matrix (Fin n) (Fin n) E).map (emb τ) := by sorry
