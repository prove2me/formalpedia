-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_crP_mem_harmK
-- name    : Formalism.L2.Pj.Crude.crP_mem_harmK
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:13.465911+00:00
-- url     : https://prove2.me/theorems/de331553-afda-4870-a7b8-88f8af3cdcb1
-- title:
--   Crude: cr P mem harm K
-- statement:
--   The Crude construction uses the cr P mem harm K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L103-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L103-L122

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

theorem Formalism.L2.Pj.Crude.crP_mem_harmK (k : Type) [Field k] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ) (cc : T → T)
    (isX : T → Prop) (hcc : ∀ τ, isX τ → cc τ ≠ τ) (hβ : Function.Injective β) :
    crP r n k β a ∈ harmK r n k cc isX (fun _ => 1) := by sorry
