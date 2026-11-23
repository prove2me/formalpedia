-- Prove2me | Theorems.Thm_Formalism_REAL_reverse_of_fn_noncompact
-- name    : Formalism.REAL.reverse_of_fn_noncompact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:09:02.336913+00:00
-- url     : https://prove2.me/theorems/7e01d2cc-75f8-4e9f-adfc-ad9f8eb05615
-- title:
--   REAL: reverse of fn noncompact
-- statement:
--   The REAL construction uses the reverse of fn noncompact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L567-L572
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L567-L572

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V)

theorem Formalism.REAL.reverse_of_fn_noncompact {j : ℕ} (α : Fin j → Fin n × Fin n) (h : ∀ i, ε (α i).1 ≠ ε (α i).2) :
    ∀ p ∈ (List.ofFn α).reverse, ε p.1 ≠ ε p.2 := by sorry
