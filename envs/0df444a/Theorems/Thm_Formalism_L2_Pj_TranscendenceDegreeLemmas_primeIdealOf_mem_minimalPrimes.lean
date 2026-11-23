-- Prove2me | Theorems.Thm_Formalism_L2_Pj_TranscendenceDegreeLemmas_primeIdealOf_mem_minimalPrimes
-- name    : Formalism.L2.Pj.TranscendenceDegreeLemmas.primeIdealOf_mem_minimalPrimes
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:26.639798+00:00
-- url     : https://prove2.me/theorems/e3612dbf-bae9-4a50-a21d-08cb14eb9ca4
-- title:
--   Transcendence Degree Lemmas: prime Ideal Of mem minimal Primes
-- statement:
--   The Transcendence Degree Lemmas construction uses the prime Ideal Of mem minimal Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/KapTrdegPfB.lean#L7-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/KapTrdegPfB.lean#L7-L30

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_KapTrdegPfA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_KapTrdegPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.TranscendenceDegreeLemmas
open AlgebraicGeometry CategoryTheory

theorem Formalism.L2.Pj.TranscendenceDegreeLemmas.primeIdealOf_mem_minimalPrimes {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) {Z : Set X}
    (hZ : Z ∈ irreducibleComponents X) (hx : hZ.1.genericPoint ∈ V) :
    (hV.primeIdealOf ⟨_, hx⟩).asIdeal ∈ minimalPrimes Γ(X, V) := by sorry
