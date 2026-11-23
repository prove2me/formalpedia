-- Prove2me | Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_eval_pow_map
-- name    : Formalism.CyclotomicNorms.CycleTypeFiniteOrder.eval_pow_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:50:17.737719+00:00
-- url     : https://prove2.me/theorems/94ee05c0-2a22-41cd-aefa-7ab83ade8177
-- title:
--   Cycle Type Finite Order: eval pow map
-- statement:
--   The Cycle Type Finite Order construction uses the eval pow map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/IrreducibilityOfRestriction.lean#L46-L49

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
variable {g : ℕ} [hg : Fact g.Prime]

theorem Formalism.CyclotomicNorms.CycleTypeFiniteOrder.eval_pow_map (p : (ZMod g)[X]) (x : Fbar g) :
    (p.map (algebraMap (ZMod g) (Fbar g))).eval (x ^ g) =
      ((p.map (algebraMap (ZMod g) (Fbar g))).eval x) ^ g := by sorry
