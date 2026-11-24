-- Prove2me | Theorems.Thm_Formalism_G0_DetValP_entry_one_nmem
-- name    : Formalism.G0.DetValP.entry_one_nmem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:06.128958+00:00
-- url     : https://prove2.me/theorems/9745b3fd-acd1-4f7a-b659-94e627309486
-- title:
--   Det Val P: entry one nmem
-- statement:
--   The Det Val P construction uses the entry one nmem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetVal.lean#L106-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetVal.lean#L106-L111

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.DetValP
open Formalism.G0
variable {K ι : Type} [Field K] [DecidableEq ι]

theorem Formalism.G0.DetValP.entry_one_nmem {R : Type} [CommRing R] {r : ℕ} (vec : ι → Bool) (S : Finset ι)
    (φ : Polynomial K →+* R) (v : ι × Fin r → R) (i : ι) (hi : i ∉ S) (a : Fin r) :
    MvPolynomial.eval₂Hom φ v (substS (K := K) vec S (1 : GL (Fin r) K) (MvPolynomial.X (i, a))) =
      v (i, a) := by sorry
