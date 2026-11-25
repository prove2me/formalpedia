-- Prove2me | Theorems.Thm_Formalism_L2_Pj_RegA_reg_vertical_e
-- name    : Formalism.L2.Pj.RegA.reg_vertical_e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:08.278805+00:00
-- url     : https://prove2.me/theorems/c1db8fcd-95fb-4ed8-941e-e15d40b647ca
-- title:
--   Reg A: reg vertical e
-- statement:
--   The Reg A construction uses the reg vertical e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RegModelA.lean#L8-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RegModelA.lean#L8-L265

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegVert
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegAVpt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.RegA
open IsLocalRing ReciprocityTheory.ChartRestriction.G.T0

theorem Formalism.L2.Pj.RegA.reg_vertical_e {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Module.Flat O A]
    [IsIntegrallyClosed A] (f : FractionRing A) (e : A) (he : e ≠ 0)
    (hf : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
      [Module.Finite O V] (φ : A →ₐ[O] V) (a b : A),
      f * algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) a → φ b ≠ 0 → φ e ≠ 0 →
      ∃ v : V, φ a = v * φ b)
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1)
    (hv : Ideal.map (algebraMap O A) (maximalIdeal O) ≤ P) :
    ∃ a s : A, s ∉ P ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a := by sorry
