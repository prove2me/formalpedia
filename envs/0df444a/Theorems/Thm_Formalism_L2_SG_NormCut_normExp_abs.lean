-- Prove2me | Theorems.Thm_Formalism_L2_SG_NormCut_normExp_abs
-- name    : Formalism.L2.SG.NormCut.normExp_abs
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:48.913314+00:00
-- url     : https://prove2.me/theorems/4f2d1c35-0b4c-4871-bb34-674be603f107
-- title:
--   Norm Cut: norm Exp abs
-- statement:
--   The Norm Cut construction uses the norm Exp abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormAsm.lean#L184-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormAsm.lean#L184-L342

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormAsm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NormCut
variable {I : Type} [Group I] [Fintype I]
set_option maxHeartbeats 800000

theorem Formalism.L2.SG.NormCut.normExp_abs {τ Rw H K Q1 Q2 R R' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] [Fintype Q1] [Fintype Q2] [Fintype R]
    [Fintype R'] (X : Formalism.FourierDecayAlt.PB.Terms τ Rw I H (PiLp 2 (fun _ : Q1 × Q2 => K))) (S : Set τ)
    (lamR : R → Q1) (lamR' : R' → Q2) (Bl : R → R' → H →L[ℂ] K)
    (hBl : ∀ x y : H, inner ℂ x y = ∑ ρ, ∑ ρ', inner ℂ (Bl ρ ρ' x) (Bl ρ ρ' y))
    (intersection_update_fsHerm_neg_one : τ → Q1 × Q2) (a : τ → K) (ιt : τ → I) (p : I → ℂ) (sR : R → I) (sR' : R' → I)
    (hop : ∀ t ρ ρ', Bl ρ ρ' (X.op t) =
      if intersection_update_fsHerm_neg_one t = (lamR ρ, lamR' ρ') then p ((sR ρ)⁻¹ * ιt t * sR' ρ') • a t else 0)
    (w : Q1 × Q2 → ℝ) (hw0 : ∀ q, 0 < w q)
    (hvec : ∀ t, X.vec t = WithLp.toLp 2 (fun q => if q = intersection_update_fsHerm_neg_one t then ((w q : ℝ) : ℂ) • a t else 0))
    (hio : ∀ t, X.io (X.rowOf t) = ιt t)
    (U : Set I) (h0 : ∀ x, x ∉ U → p x = 0) (hr : ∀ x, ∀ u ∈ U, p (x * u) = p x * p u)
    (hl : ∀ x, ∀ u ∈ U, p (u * x) = p u * p x) (hn : ∀ u ∈ U, conj (p u) * p u = 1)
    (hGG : ∀ i j, X.GG i j = conj (gamOf U p (j⁻¹ * i)))
    (A : Q1 → Set I) (A' : Q2 → Set I)
    (hA : ∀ q, Function.Bijective
      (fun x : A q × {ρ // lamR ρ = q} × U => (x.1 : I) * sR x.2.1.1 * (x.2.2 : I)))
    (hA' : ∀ q, Function.Bijective
      (fun x : A' q × {ρ // lamR' ρ = q} × U => (x.1 : I) * sR' x.2.1.1 * (x.2.2 : I)))
    (hwA : ∀ q, w q ^ 2 = ((Nat.card (A q.1) : ℝ) * (Nat.card (A' q.2) : ℝ))⁻¹)
    (hsatL : ∀ q, ∀ b ∈ A q.1, ∀ i j, inner ℂ (Zs S intersection_update_fsHerm_neg_one ιt a q (b * i)) (Zs S intersection_update_fsHerm_neg_one ιt a q (b * j)) =
      inner ℂ (Zs S intersection_update_fsHerm_neg_one ιt a q i) (Zs S intersection_update_fsHerm_neg_one ιt a q j))
    (hsatR : ∀ q, ∀ b ∈ A' q.2, ∀ i j, inner ℂ (Zs S intersection_update_fsHerm_neg_one ιt a q (i * b⁻¹)) (Zs S intersection_update_fsHerm_neg_one ιt a q (j * b⁻¹)) =
      inner ℂ (Zs S intersection_update_fsHerm_neg_one ιt a q i) (Zs S intersection_update_fsHerm_neg_one ιt a q j))
    (hsum : Summable fun t => ‖X.op t‖) (hsumv : Summable fun t => ‖X.vec t‖) :
    X.NormExpansionOn S := by sorry
