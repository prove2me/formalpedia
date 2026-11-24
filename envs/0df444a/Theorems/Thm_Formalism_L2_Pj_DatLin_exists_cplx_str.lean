-- Prove2me | Theorems.Thm_Formalism_L2_Pj_DatLin_exists_cplx_str
-- name    : Formalism.L2.Pj.DatLin.exists_cplx_str
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:48.749219+00:00
-- url     : https://prove2.me/theorems/44517642-ea44-4bd2-90ab-5fad0fc06bb3
-- title:
--   Dat Lin: exists cplx str
-- statement:
--   The Dat Lin construction uses the exists cplx str property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DatMat.lean#L53-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DatMat.lean#L53-L103

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DatMat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.DatLin
open Matrix Complex
variable {m : Type} [Fintype m] [DecidableEq m]

theorem Formalism.L2.Pj.DatLin.exists_cplx_str {n : Type} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (p q : ℕ)
    (e : n ≃ Fin p ⊕ Fin q) (P : GL (Fin p ⊕ Fin q) ℂ)
    (hP : ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).map (starRingEnd ℂ))ᵀ * H.reindex e e *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Matrix.fromBlocks 1 0 0 (-1)) :
    ∃ K : Matrix n n ℂ, (∀ u, K *ᵥ (K *ᵥ u) = -u) ∧
      (∀ u w, star (K *ᵥ u) ⬝ᵥ (H *ᵥ (K *ᵥ w)) = star u ⬝ᵥ (H *ᵥ w)) ∧
      (∀ u : n → ℂ, u ≠ 0 → ∃ ρ : ℝ, 0 < ρ ∧ star (K *ᵥ u) ⬝ᵥ (H *ᵥ u) = -(Complex.I * ρ)) ∧
      K.trace = Complex.I * ((p : ℂ) - q) := by sorry
