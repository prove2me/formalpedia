-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb_zero
-- name    : Formalism.FrobeniusOrbits.Cond.emb_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T14:10:36.729208+00:00
-- url     : https://prove2.me/theorems/72a4909d-0a48-44fa-b370-01ca6b4830f6
-- title:
--   Cond: emb zero
-- statement:
--   The Cond construction uses the emb zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/EqZeroOfNegEq.lean#L273-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/EqZeroOfNegEq.lean#L273-L303

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Cond

theorem Formalism.FrobeniusOrbits.Cond.emb_zero {q d : ℕ} [Fact q.Prime] [Fact d.Prime] (hq4 : q % 4 = 3) (hd4 : d % 4 = 3)
    {L : Type} [Field L] [NumberField L] {ζ a b : L} (h : IsLayer (0 + 2) q d ζ a b)
    {N : ℕ} [NeZero N] (hq : q ∣ N) (hd : d ∣ N) :
    Nonempty (hostE ζ a b →ₐ[ℚ] Cyc N) := by sorry
