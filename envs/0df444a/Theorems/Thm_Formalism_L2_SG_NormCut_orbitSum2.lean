-- Prove2me | Theorems.Thm_Formalism_L2_SG_NormCut_orbitSum2
-- name    : Formalism.L2.SG.NormCut.orbitSum2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:44.504707+00:00
-- url     : https://prove2.me/theorems/0921c4db-b5e4-4b20-a264-65c0c865bda2
-- title:
--   Norm Cut: orbit Sum2
-- statement:
--   The Norm Cut construction uses the orbit Sum2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormAsm.lean#L71-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/NormAsm.lean#L71-L84

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
variable {I : Type*} [Group I] [Fintype I]

theorem Formalism.L2.SG.NormCut.orbitSum2 {C C' : Type*} [Fintype C] [Fintype C'] (A A' U : Set I) (s : C → I) (s' : C' → I)
    (hb : Function.Bijective (fun x : A × C × U => (x.1 : I) * s x.2.1 * (x.2.2 : I)))
    (hb' : Function.Bijective (fun x : A' × C' × U => (x.1 : I) * s' x.2.1 * (x.2.2 : I))) (f : I → I → ℂ)
    (hL : ∀ x y, ∀ a ∈ A, ∀ w ∈ U, f (a * x * w) y = f x y)
    (hR : ∀ x y, ∀ a ∈ A', ∀ w ∈ U, f x (a * y * w) = f x y) :
    ∑ x : I, ∑ y : I, f x y =
      ((Nat.card A : ℂ) * (Nat.card U : ℂ)) * ((Nat.card A' : ℂ) * (Nat.card U : ℂ)) *
        ∑ c : C, ∑ c' : C', f (s c) (s' c') := by sorry
