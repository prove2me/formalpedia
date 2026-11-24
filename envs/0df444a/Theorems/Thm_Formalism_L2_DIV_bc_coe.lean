-- Prove2me | Theorems.Thm_Formalism_L2_DIV_bc_coe
-- name    : Formalism.L2.DIV.bc_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:35.347726+00:00
-- url     : https://prove2.me/theorems/1aa4f5dc-2416-4ead-9066-6b69aa5689ed
-- title:
--   DIV: bc coe
-- statement:
--   The DIV construction uses the bc coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L270-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoefModLemmas.lean#L270-L271

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions

theorem Formalism.L2.DIV.bc_coe {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (φ : A →+* B) (g : GL (Fin n) A) :
    ((Formalism.UG.bc φ g : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) = (g : Matrix (Fin n) (Fin n) A).map φ := by sorry
