-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_ch_split
-- name    : Formalism.L2.FormalSeriesBounds.S4.ch_split
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:44.667024+00:00
-- url     : https://prove2.me/theorems/11bdf19b-6dd1-4373-ae0b-81d9b57b2292
-- title:
--   S4: ch split
-- statement:
--   The S4 construction uses the ch split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ExistsStrictMonoMinor.lean#L444-L485
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ExistsStrictMonoMinor.lean#L444-L485

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

theorem Formalism.L2.FormalSeriesBounds.S4.ch_split (v : AddValuation R (WithTop ℝ)) (hv : ∀ x, 0 ≤ v x)
    {d : ℕ} (hd : d ≠ 0) (l : ℕ) (hl : l.Prime) (hlodd : Odd l)
    (r n j j' rh h P : ℕ) (hP : P + j' = r) (hh : h + rh = r) (hrh : rh ≤ j')
    (p : ZMod d → ℕ) (hp : ∀ τ, p τ = P)
    (a : ZMod d) (α : Matrix (Fin (p a)) (Fin h) R)
    (S : Matrix (Fin n) (Fin (p a)) R) (W : Matrix (Fin (p a)) (Fin n) R) (hSW : S * W = 1)
    (l1 l2 : ZMod d → ℝ) (hDET : CorDET l p l1 l2 a) (hAi : ThmAi l r rh p l2 a)
    (hAiii : ThmAiii v α (l1 a)) :
    (lenCoker v α ≤ ((((j' : ℝ) - rh) / ((l : ℝ) - 1) : ℝ) : WithTop ℝ) ∧
      ((j' : ℝ) - rh) / ((l : ℝ) - 1) ≤ ((j : ℝ) + j') / ((l : ℝ) - 1)) ∧
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
              (((y : ℝ) * (((j' : ℝ) - rh) / ((l : ℝ) - 1)) : ℝ) : WithTop ℝ) := by sorry
