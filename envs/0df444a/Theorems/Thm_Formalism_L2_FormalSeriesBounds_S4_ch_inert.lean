-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_ch_inert
-- name    : Formalism.L2.FormalSeriesBounds.S4.ch_inert
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:56.878426+00:00
-- url     : https://prove2.me/theorems/35e67eb5-1c60-4c68-a877-fb165817e4ba
-- title:
--   S4: ch inert
-- statement:
--   The S4 construction uses the ch inert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ExistsStrictMonoMinor.lean#L383-L442
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ExistsStrictMonoMinor.lean#L383-L442

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

theorem Formalism.L2.FormalSeriesBounds.S4.ch_inert (v : AddValuation R (WithTop ℝ)) (hv : ∀ x, 0 ≤ v x)
    {d : ℕ} (hd : Even d) (l : ℕ) (hl : l.Prime) (hlodd : Odd l)
    (r n j j' rh h : ℕ) (hr : r = n + j + j') (hh : h + rh = r) (hrh : rh ≤ j')
    (big : ZMod d → Prop) (halt : ∀ b, big (b + 1) ↔ ¬ big b) (p : ZMod d → ℕ)
    (hpb : ∀ b, big b → p b = n + j) (hps : ∀ b, ¬ big b → p b = j')
    (a : ZMod d) (ha : big a) (α : Matrix (Fin (p a)) (Fin h) R)
    (S : Matrix (Fin n) (Fin (p a)) R) (W : Matrix (Fin (p a)) (Fin n) R) (hSW : S * W = 1)
    (l1 l2 : ZMod d → ℝ) (hDET : CorDET l p l1 l2 a) (hAi : ThmAi l r rh p l2 a)
    (hAiii : ThmAiii v α (l1 a)) :
    (lenCoker v α ≤ (xInert l r j' rh : WithTop ℝ) ∧
      xInert l r j' rh = ((r : ℝ) - j' - rh) * gam l + ((j' : ℝ) - rh) * rho l ∧
      xInert l r j' rh ≤ (n : ℝ) * gam l + ((j : ℝ) + j') / ((l : ℝ) - 1)) ∧
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
              (((y : ℝ) * xInert l r j' rh : ℝ) : WithTop ℝ) := by sorry
