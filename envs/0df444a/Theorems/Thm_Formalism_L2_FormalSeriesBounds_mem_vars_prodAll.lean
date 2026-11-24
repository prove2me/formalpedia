-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_mem_vars_prodAll
-- name    : Formalism.L2.FormalSeriesBounds.mem_vars_prodAll
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:50.698696+00:00
-- url     : https://prove2.me/theorems/40b4b29d-ddf0-49d8-9c03-4df23dba5fdf
-- title:
--   Formal Series Bounds: mem vars prod All
-- statement:
--   The Formal Series Bounds construction uses the mem vars prod All property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/MemVarsProdAll.lean#L37-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/MemVarsProdAll.lean#L37-L49

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} {N K : ℕ} {what₂ : Fin K → ℕ}

theorem Formalism.L2.FormalSeriesBounds.mem_vars_prodAll {pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N} {P : ∀ i, MvPolynomial (Fin (what₂ i) × WV I) C}
    {ρ : Fin N} {w : WV I} (h : (ρ, w) ∈ (prodAll pl P).vars) :
    ∃ s : Σ i : Fin K, Fin (what₂ i), pl s = ρ ∧ (s.2, w) ∈ (P s.1).vars := by sorry
