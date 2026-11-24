-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_crSig_ne
-- name    : Formalism.L2.Pj.Crude.crSig_ne
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:00.279414+00:00
-- url     : https://prove2.me/theorems/f7404da2-34fb-4752-8825-3f73dd54297d
-- title:
--   Crude: cr Sig ne
-- statement:
--   The Crude construction uses the cr Sig ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L138-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L138-L141

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPolynomial Formalism.L2.Pj
variable {T : Type} [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ)
variable {r n}

theorem Formalism.L2.Pj.Crude.crSig_ne {τ σ : T} (h : τ ≠ σ) {x : Fin (r τ)} {y : Fin n} {i : Fin (r σ)} :
    ¬ ∃ b : Fin n, (⟨τ, x, y⟩ : Letter T r n) = ⟨σ, i, b⟩ := by sorry
