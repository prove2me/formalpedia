-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_kindAll_pl
-- name    : Formalism.L2.FormalSeriesBounds.kindAll_pl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:58:34.807855+00:00
-- url     : https://prove2.me/theorems/19664734-9aaf-4844-b306-887f5e3d432c
-- title:
--   Formal Series Bounds: kind All pl
-- statement:
--   The Formal Series Bounds construction uses the kind All pl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/MemVarsProdAll.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/MemVarsProdAll.lean#L29-L35

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

theorem Formalism.L2.FormalSeriesBounds.kindAll_pl {pl : (Σ i : Fin K, Fin (what₂ i)) → Fin N} (hpl : Function.Injective pl)
    (kind : ∀ i, Fin (what₂ i) → Knd d) (s : Σ i : Fin K, Fin (what₂ i)) : kindAll pl kind (pl s) = kind s.1 s.2 := by sorry
