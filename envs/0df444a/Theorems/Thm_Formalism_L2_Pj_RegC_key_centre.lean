-- Prove2me | Theorems.Thm_Formalism_L2_Pj_RegC_key_centre
-- name    : Formalism.L2.Pj.RegC.key_centre
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:47:25.009162+00:00
-- url     : https://prove2.me/theorems/cac27a6e-c300-46a8-bd82-ac5d26800ff1
-- title:
--   Reg C: key centre
-- statement:
--   The Reg C construction uses the key centre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RegModelC.lean#L55-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RegModelC.lean#L55-L77

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.RegC
open IsLocalRing ReciprocityTheory.ChartRestriction.G.T0

theorem Formalism.L2.Pj.RegC.key_centre {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Module.Flat O A]
    [IsIntegrallyClosed A] (f : FractionRing A) (e : A) (he : e ≠ 0)
    (hf : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
      [Module.Finite O V] (φ : A →ₐ[O] V) (a b : A),
      f * algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) a → φ b ≠ 0 → φ e ≠ 0 →
      ∃ v : V, φ a = v * φ b)
    (qq : Ideal A) [qq.IsPrime] (hqq : qq ⊔ Ideal.map (algebraMap O A) (maximalIdeal O) ≠ ⊤) :
    ∃ a s : A, s ∉ qq ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a := by sorry
