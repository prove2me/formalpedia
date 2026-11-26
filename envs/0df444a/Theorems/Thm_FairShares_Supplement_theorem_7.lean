-- Prove2me | Theorems.Thm_FairShares_Supplement_theorem_7
-- name    : FairShares.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:31:12.971229+00:00
-- url     : https://prove2.me/theorems/1a59c696-d437-46f2-9ef8-e1246fe9922a
-- title:
--   Theorem 7: feasibility of the nested share $NS_{n,3}$
-- statement:
--   For additive valuations and every $n\ge3$, the nested share $NS_{n,3}$ is a feasible share. Moreover, one uniform polynomial-time algorithm finds an allocation giving every agent at least her $NS_{n,3}$ share.
--
--   This is the feasibility component used in the full guarantees of Theorem 6.
--
--   Differences from the source:
--   - encoding: finite item and agent sets → goods `Fin m`, agents `Fin n`, allocations `Fin m → Fin n`, with the source's explicit `3 ≤ n`; reason: maps are exactly labelled partitions into possibly empty bundles
--   - encoding: polynomial-time acceptable allocation → one Cook Turing machine uniform over every n ≥ 3 on binary-encoded nonnegative rational profiles; reason: this is the finite input model and preserves the theorem's uniform quantifier over n
--   - encoding: NS_n,3 → `nestedShare n 3`, the exact rank-interval family of Section 6.3 with every compatible tie order; reason: equal singleton values make tie breaking immaterial for additive valuations
-- source:
--   Babaioff & Feige, arXiv:2205.07519v1, Theorem 7, p.25

import Mathlib
import Definitions.Def_FairShares_IsAdditive
import Definitions.Def_FairShares_IsShareAt
import Definitions.Def_FairShares_FeasibleAt
import Definitions.Def_FairShares_Supplement_nestedShare
import Definitions.Def_FairShares_bundle
import Definitions.Def_CookPvsNP_defs

set_option autoImplicit false

namespace FairShares.Supplement

/-- **Theorem 7: feasibility of `NS_{n,3}`.**
Babaioff & Feige, *Fair Shares: Feasibility, Domination and Incentives*,
arXiv:2205.07519v1, Theorem 7, p.25.

For every `n ≥ 3`, the nested share `NS_{n,3}` is a feasible share for additive valuations, and
one uniform polynomial-time algorithm finds an acceptable allocation.

**Formalization Note.** Feasibility covers every item count and every profile of real additive
valuations.  The algorithmic clause uses the paper's finite input convention: binary-encoded
nonnegative rational item values, with one Cook machine uniform in both `m` and `n`. -/
theorem theorem_7 :
    let encNat : ℕ → List Bool := fun a =>
      (Nat.bits a).flatMap (fun b => [false, b]) ++ [true, true]
    let encInt : ℤ → List Bool := fun z => [decide (z < 0)] ++ encNat z.natAbs
    let encRat : ℚ → List Bool := fun r => encInt r.num ++ encNat r.den
    (∀ (n : ℕ), 3 ≤ n → ∀ m,
      FairShares.IsShareAt {v | FairShares.IsAdditive v} (nestedShare n 3 m)) ∧
    (∀ (n : ℕ), 3 ≤ n → ∀ m,
      FairShares.FeasibleAt n {v | FairShares.IsAdditive v} (nestedShare n 3 m)) ∧
    ∃ run : List Bool → List Bool, CookPvsNP.PolyTimeComputable run ∧
      ∀ (m n : ℕ), 3 ≤ n → ∀ w : Fin n → Fin m → ℚ, (∀ i g, 0 ≤ w i g) →
        ∃ A : Fin m → Fin n,
          run (encNat m ++ encNat n ++
            (List.ofFn (fun i : Fin n => (List.ofFn (w i)).flatMap encRat)).flatten) =
              (List.ofFn A).flatMap (fun i => encNat i.val) ∧
          ∀ i : Fin n,
            nestedShare n 3 m (fun S => ∑ g ∈ S, (w i g : ℝ)) ≤
              ∑ g ∈ FairShares.bundle A i, (w i g : ℝ) := by sorry

end FairShares.Supplement
