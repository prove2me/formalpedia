-- Prove2me | Theorems.Thm_FairShares_Supplement_theorem_6
-- name    : FairShares.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:30:39.951801+00:00
-- url     : https://prove2.me/theorems/1487aa9b-ab89-5eaf-83d0-891dbc5c6d3e
-- title:
--   Theorem 6: guarantees of the nested share $NS_{n,3}$
-- statement:
--   For every $n\ge3$ and additive valuations over goods, the same nested share $NS_{n,3}$ is a share, is self-maximizing, and is polynomial-time computable. For every valuation $v$,
--   $$
--   NS_{n,3}(v)\ge\frac{2n}{3n-1}\operatorname{MMS}_n(v),
--   $$
--   and when $n\le4$ it also satisfies $NS_{n,3}(v)\ge\frac45\operatorname{MMS}_n(v)$. The share is feasible, and an acceptable allocation can be found in polynomial time.
--
--   Differences from the source:
--   - encoding: q = 3 belongs to [n] implicitly → an explicit hypothesis `3 ≤ n`; reason: this excludes exactly the agent counts for which NS_n,3 is undefined
--   - encoding: nested prefix/suffix partitions after arbitrary tie breaking → half-open intervals of ranks in `Fin m`, increasing on the prefix and reversed on the suffix, with the first n-3 prefix parts singleton; the value ranges over every compatible sorted permutation; reason: this is Section 6.3 and makes tie independence explicit
--   - encoding: polynomial-time share computation and acceptable allocation → two separate Cook-machine clauses, each uniform over all n ≥ 3 and binary-encoded nonnegative rational item values; reason: Lemma 18 is polynomial in m and n, and Theorem 6 states the two outputs separately
--   - encoding: MMS_n(v) → the published `LittleCharity.MMS.mms v n univ`; reason: Definition 1 for positive n
-- source:
--   Babaioff & Feige, arXiv:2205.07519v1, Theorem 6, p.22; Lemma 18 and approximation analysis, pp.37-47

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_FairShares_IsAdditive
import Definitions.Def_FairShares_IsShareAt
import Definitions.Def_FairShares_FeasibleAt
import Definitions.Def_FairShares_SelfMaxAt
import Definitions.Def_FairShares_Supplement_nestedShare
import Definitions.Def_FairShares_bundle
import Definitions.Def_CookPvsNP_defs

set_option autoImplicit false

namespace FairShares.Supplement

/-- **Theorem 6: guarantees of the nested share `NS_{n,3}`.**
Babaioff & Feige, *Fair Shares: Feasibility, Domination and Incentives*,
arXiv:2205.07519v1, Theorem 6, p.22 (supporting analysis pp.37--47).

Uniformly for every `n ≥ 3`, the same nested share is a share, is self-maximizing, is
polynomial-time computable, is at least `2n/(3n-1)` times MMS and at least `4/5` times MMS when
`n ≤ 4`, is feasible, and admits a polynomial-time acceptable-allocation algorithm.

**Formalization Note.** `3 ≤ n` is the domain condition implicit in the notation `q = 3 ∈ [n]`.
The two computational conjuncts are distinct and each uses one Cook machine uniformly over all
`n ≥ 3`, on binary-encoded nonnegative rational item values.  All other conjuncts range over
every real additive valuation. -/
theorem theorem_6 :
    let encNat : ℕ → List Bool := fun a =>
      (Nat.bits a).flatMap (fun b => [false, b]) ++ [true, true]
    let encInt : ℤ → List Bool := fun z => [decide (z < 0)] ++ encNat z.natAbs
    let encRat : ℚ → List Bool := fun r => encInt r.num ++ encNat r.den
    (∀ (n : ℕ), 3 ≤ n → ∀ m,
      FairShares.IsShareAt {v | FairShares.IsAdditive v} (nestedShare n 3 m)) ∧
    (∀ (n : ℕ), 3 ≤ n → ∀ m,
      FairShares.SelfMaxAt {v | FairShares.IsAdditive v} (nestedShare n 3 m)) ∧
    (∃ run : List Bool → List Bool, CookPvsNP.PolyTimeComputable run ∧
      ∀ (m n : ℕ), 3 ≤ n → ∀ w : Fin m → ℚ, (∀ g, 0 ≤ w g) →
        ∃ r : ℚ, (r : ℝ) = nestedShare n 3 m (fun S => ∑ g ∈ S, (w g : ℝ)) ∧
          run (encNat m ++ encNat n ++ (List.ofFn w).flatMap encRat) = encRat r) ∧
    (∀ (n : ℕ), 3 ≤ n → ∀ (m : ℕ) (v : Finset (Fin m) → ℝ),
      FairShares.IsAdditive v →
        ((2 * (n : ℝ)) / (3 * (n : ℝ) - 1)) *
            LittleCharity.MMS.mms v n Finset.univ ≤ nestedShare n 3 m v) ∧
    (∀ (n : ℕ), 3 ≤ n → n ≤ 4 → ∀ (m : ℕ) (v : Finset (Fin m) → ℝ),
      FairShares.IsAdditive v →
        (4 / 5 : ℝ) * LittleCharity.MMS.mms v n Finset.univ ≤ nestedShare n 3 m v) ∧
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
