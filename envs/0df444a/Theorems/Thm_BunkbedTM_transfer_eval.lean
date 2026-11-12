-- Prove2me | Theorems.Thm_BunkbedTM_transfer_eval
-- name    : BunkbedTM.transfer_eval
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T16:00:46.48199+00:00
-- url     : https://prove2.me/theorems/eddcd9b7-9b95-4f20-83e4-5562bb636386
-- title:
--   The six-step transfer matrix for Hollom's hypergraph
-- statement:
--   Summing any function of the induced profile against the Wierman--Ziff weight of a level configuration collapses from $5^6 = 15625$ configurations onto the $47$ reachable profiles.
--
--   Hollom's six hyperedges can be listed along the path $\rho$ of Eq. [5], $0 \to 2 \to 5 \to 4 \to 3 \to 7 \to 9$, so that every intermediate path vertex lies in exactly two consecutive hyperedges. Sweeping them in that order, the only information that must be carried forward is the partition induced on the four special vertices $\{0, 1, 6, 8\}$ together with the current path vertex — five slots — and a spent path vertex can be forgotten as soon as its second hyperedge has been processed. That is the transfer matrix `step`.
--
--   Iterating it six times from the initial state visits only $1, 5, 13, 34, 41, 41, 47$ distinct states, and the total weight accumulated at each of the $47$ terminal profiles is a homogeneous polynomial of degree $6$ in the four state probabilities $x = P_{abc}$, $y = P_{a|b|c}$, $z = P_{a|bc}$, $u = P_{ab|c} = P_{ac|b}$ — recorded as `wFinal`. The hypothesis `hsym` is the symmetry $P_{ab|c} = P_{ac|b}$ under which the model has four rather than five parameters.
-- source:
--   Gladkov, Pak, Zimin, *The bunkbed conjecture is false*, PNAS 122 (2025) no. 24, e2420725122; Section 3, Lemma 3.3 and Hollom's 3-uniform hypergraph (Fig. 1), with the path $\rho$ of Eq. [5].

import Definitions.Def_BunkbedTransferTables
open Bunkbed Bunkbed.Hyper Bunkbed.TM SimpleGraph Finset

theorem BunkbedTM.transfer_eval (P : WZ → ℚ) (hsym : P WZ.ab_c = P WZ.ac_b)
    (G : St → ℚ) :
    (∑ t₀ : WZ, ∑ t₁ : WZ, ∑ t₂ : WZ, ∑ t₃ : WZ, ∑ t₄ : WZ, ∑ t₅ : WZ,
        (P t₀ * P t₁ * P t₂ * P t₃ * P t₄ * P t₅)
          * G (step 5 t₅ (step 4 t₄ (step 3 t₃ (step 2 t₂ (step 1 t₁ (step 0 t₀ stInit)))))))
      = ∑ j : Fin 47, wFinal j (P WZ.abc) (P WZ.a_b_c) (P WZ.a_bc) (P WZ.ab_c)
          * G (stFinal j) := by sorry
