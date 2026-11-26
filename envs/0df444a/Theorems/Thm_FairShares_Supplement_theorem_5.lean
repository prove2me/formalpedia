-- Prove2me | Theorems.Thm_FairShares_Supplement_theorem_5
-- name    : FairShares.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:30:06.215797+00:00
-- url     : https://prove2.me/theorems/e07066c6-eaad-511b-b38d-1d45025ad710
-- title:
--   Theorem 5: two-agent self-maximizing $\operatorname{PTAS}(\varepsilon)$ share
-- statement:
--   Fix $\varepsilon>0$. For two agents with additive valuations over goods, the paper's $\operatorname{PTAS}(\varepsilon)$ share is a share, is self-maximizing, is computable in polynomial time for fixed $\varepsilon$, and satisfies
--   $$
--   \operatorname{PTAS}(\varepsilon)(v)\ge(1-\varepsilon)\operatorname{MMS}_2(v).
--   $$
--   It is feasible, and an acceptable allocation can be found in polynomial time.
--
--   Differences from the source:
--   - encoding: arbitrary item names, arbitrary tie breaking, and the proof's restricted partitions → items `Fin m`; the value ranges over every non-increasing rank permutation and the exact family whose first bundle has any top-k subset and a suffix of the remaining ranks, with both exact-MMS exceptional cases retained; reason: this is name-independent and equal-value tie orders induce the same additive bundle values
--   - encoding: polynomial time for fixed epsilon on finitely encoded item values → separate Cook machines for exact share-value output and acceptable-allocation output on binary-encoded nonnegative rational item values; reason: p.21 explicitly measures the input bits and separately claims both algorithms; the machines may depend on fixed epsilon
--   - encoding: MMS for two agents → the published `LittleCharity.MMS.mms v 2 univ`; reason: it is the maximum over labelled two-way partitions of the minimum bundle value
-- source:
--   Babaioff & Feige, arXiv:2205.07519v1, Theorem 5 and proof, pp.20-21

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_FairShares_IsAdditive
import Definitions.Def_FairShares_IsShareAt
import Definitions.Def_FairShares_FeasibleAt
import Definitions.Def_FairShares_SelfMaxAt
import Definitions.Def_FairShares_Supplement_ptasShare
import Definitions.Def_FairShares_bundle
import Definitions.Def_CookPvsNP_defs

set_option autoImplicit false

namespace FairShares.Supplement

/-- **Theorem 5: the two-agent self-maximizing PTAS share.**
Babaioff & Feige, *Fair Shares: Feasibility, Domination and Incentives*,
arXiv:2205.07519v1, Theorem 5, p.20 (proof pp.20--21).

For every fixed `ε > 0`, `ptasShare ε` is a share for two additive agents, is self-maximizing,
is polynomial-time computable, is at least `(1-ε)` times two-agent MMS, is feasible, and admits
a polynomial-time acceptable-allocation algorithm.

**Formalization Note.** The exact-MMS cases `m < 3/ε` and an item above `2v(M)/3` are part of
`ptasShare`, not hypotheses.  Both computational clauses use explicit finite binary encodings of
nonnegative rational item values, while the mathematical clauses cover every real additive
valuation.  The value and allocation algorithms are separate predicates. -/
theorem theorem_5 (ε : ℝ) (hε : 0 < ε) :
    let encNat : ℕ → List Bool := fun a =>
      (Nat.bits a).flatMap (fun b => [false, b]) ++ [true, true]
    let encInt : ℤ → List Bool := fun z => [decide (z < 0)] ++ encNat z.natAbs
    let encRat : ℚ → List Bool := fun r => encInt r.num ++ encNat r.den
    (∀ m, FairShares.IsShareAt {v | FairShares.IsAdditive v} (ptasShare ε m)) ∧
    (∀ m, FairShares.SelfMaxAt {v | FairShares.IsAdditive v} (ptasShare ε m)) ∧
    (∃ run : List Bool → List Bool, CookPvsNP.PolyTimeComputable run ∧
      ∀ (m : ℕ) (w : Fin m → ℚ), (∀ g, 0 ≤ w g) →
        ∃ r : ℚ, (r : ℝ) = ptasShare ε m (fun S => ∑ g ∈ S, (w g : ℝ)) ∧
          run (encNat m ++ encNat 2 ++ (List.ofFn w).flatMap encRat) = encRat r) ∧
    (∀ (m : ℕ) (v : Finset (Fin m) → ℝ), FairShares.IsAdditive v →
      (1 - ε) * LittleCharity.MMS.mms v 2 Finset.univ ≤ ptasShare ε m v) ∧
    (∀ m, FairShares.FeasibleAt 2 {v | FairShares.IsAdditive v} (ptasShare ε m)) ∧
    ∃ run : List Bool → List Bool, CookPvsNP.PolyTimeComputable run ∧
      ∀ (m : ℕ) (w : Fin 2 → Fin m → ℚ), (∀ i g, 0 ≤ w i g) →
        ∃ A : Fin m → Fin 2,
          run (encNat m ++ encNat 2 ++
            (List.ofFn (fun i : Fin 2 => (List.ofFn (w i)).flatMap encRat)).flatten) =
              (List.ofFn A).flatMap (fun i => encNat i.val) ∧
          ∀ i : Fin 2,
            ptasShare ε m (fun S => ∑ g ∈ S, (w i g : ℝ)) ≤
              ∑ g ∈ FairShares.bundle A i, (w i g : ℝ) := by sorry

end FairShares.Supplement
