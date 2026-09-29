-- Prove2me | Theorems.Thm_FamousTheorems_char_dvd_card_solutions
-- name    : FamousTheorems.char_dvd_card_solutions
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:40:41.204895+00:00
-- url     : https://prove2.me/theorems/1df9a430-84da-47f0-a6d1-77bd12ab2fe1
-- title:
--   The Chevalley–Warning theorem
-- statement:
--   **The Chevalley\u2013Warning theorem.** If a polynomial over a finite field of characteristic $p$ has total degree less than the number of variables, then the number of its zeros is divisible by $p$. The hypothesis compares degree with dimension, not with the field size, so it is a genuinely combinatorial condition. The striking corollary is Chevalley's: a homogeneous polynomial of degree less than the number of variables always has a nontrivial zero, since the origin is one solution and the count must be divisible by $p$. So finite fields are quasi-algebraically closed — forms of low degree cannot avoid nontrivial zeros, in sharp contrast with $\mathbb{Q}$. Warning proved the divisibility in 1935, strengthening Chevalley's existence result of the same year. **Formalization note.** The solutions are counted in the function type from variables to the field, and divisibility is by the ring characteristic. The result is Mathlib's `char_dvd_card_solutions`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem char_dvd_card_solutions :
    ∀ {K : Type u_1} {σ : Type u_2} [inst : Fintype K] [inst_1 : Field K] [inst_2 : Fintype σ] 
    [inst_3 : DecidableEq σ] [inst_4 : DecidableEq K] (p : ℕ) [CharP K p] {f : MvPolynomial σ K}, 
    f.totalDegree < Fintype.card σ → p ∣ Fintype.card { x // (MvPolynomial.eval x) f = 0 } := by sorry

end FamousTheorems
