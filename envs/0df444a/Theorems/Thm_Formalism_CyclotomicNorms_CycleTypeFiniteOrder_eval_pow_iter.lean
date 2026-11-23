-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_eval_pow_iter
-- name    : Formalism.CyclotomicNorms.CycleTypeFiniteOrder.eval_pow_iter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:44.046272+00:00
-- url     : https://prove2.me/theorems/13083f40-9e6d-477d-928b-e83f2331adc3
-- title:
--   Cycle Type Finite Order: eval pow iter
-- statement:
--   The Cycle Type Finite Order construction uses the eval pow iter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L182-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L182-L187

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {g : ℕ} [hg : Fact g.Prime] {N : ℕ} {f : (ZMod g)[X]}
variable {r : Fin N → Fbar g} {σ : Equiv.Perm (Fin N)}

theorem Formalism.CyclotomicNorms.CycleTypeFiniteOrder.eval_pow_iter (p : (ZMod g)[X]) (x : Fbar g)
    (hx : (p.map (algebraMap (ZMod g) (Fbar g))).eval x = 0) (n : ℕ) :
    (p.map (algebraMap (ZMod g) (Fbar g))).eval (x ^ (g ^ n)) = 0 := by sorry
