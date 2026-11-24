-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_ch_minor
-- name    : Formalism.L2.FormalSeriesBounds.S4.ch_minor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:50.057662+00:00
-- url     : https://prove2.me/theorems/8a2e9dc0-8f95-457c-9c1a-894a38b98c0b
-- title:
--   S4: ch minor
-- statement:
--   The S4 construction uses the ch minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ExistsStrictMonoMinor.lean#L330-L381
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ExistsStrictMonoMinor.lean#L330-L381

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.S4
variable {R : Type*} [CommRing R]

theorem Formalism.L2.FormalSeriesBounds.S4.ch_minor (v : AddValuation R (WithTop ℝ)) (hv : ∀ x, 0 ≤ v x) {n p h : ℕ}
    (S : Matrix (Fin n) (Fin p) R) (W : Matrix (Fin p) (Fin n) R) (hSW : S * W = 1)
    (α : Matrix (Fin p) (Fin h) R) (x : ℝ) (hx : lenCoker v α ≤ (x : WithTop ℝ)) :
    ∃ f : Fin n → Fin h, StrictMono f ∧
      v (Matrix.of fun k c => (S * α) c (f k)).det ≤ lenCoker v α ∧
      ∀ (F : Type) [CommRing F] [Algebra R F] (D : Fin n → Fin n → Derivation R F F)
        (χ : Fin n → F) (ev : F →ₐ[R] R),
        (∀ ρ c σ, D ρ c (χ σ) = (if σ = ρ then (S * α) c (f ρ) else 0) • χ σ) →
        (∀ σ, ev (χ σ) = 1) →
        ∀ y : ℕ,
          ev (((detOp fun ρ c => (D ρ c : F →ₗ[R] F)) ^ y) (∏ σ, χ σ)) =
              (Matrix.of fun k c => (S * α) c (f k)).det ^ y ∧
            v ((Matrix.of fun k c => (S * α) c (f k)).det ^ y) ≤
              (((y : ℝ) * x : ℝ) : WithTop ℝ) := by sorry
