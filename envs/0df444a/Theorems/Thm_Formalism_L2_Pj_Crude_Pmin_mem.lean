-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_Pmin_mem
-- name    : Formalism.L2.Pj.Crude.Pmin_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:16.167812+00:00
-- url     : https://prove2.me/theorems/bd127d4d-cfa1-4d0e-a5e1-07e2c80fb087
-- title:
--   Crude: Pmin mem
-- statement:
--   The Crude construction uses the Pmin mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L533-L541
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeMin.lean#L533-L541

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
variable (k : Type) [Field k] [CharZero k] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ)

theorem Formalism.L2.Pj.Crude.Pmin_mem (O : Subring k) (cc : T → T) (isX : T → Prop) (hcc : ∀ τ, isX τ → cc τ ≠ τ)
    (hβ : Function.Injective β) (ha : Dom r a) :
    MvPolynomial.map (Int.castRingHom k) (Pmin r n β a) ∈ HaO r n k O cc isX a := by sorry
