-- Prove2me | Theorems.Thm_FairShares_Supplement_theorem_3
-- name    : FairShares.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-26T21:29:30.296516+00:00
-- url     : https://prove2.me/theorems/bc307e2f-f882-5278-bc3c-f04641750565
-- title:
--   Theorem 3: polynomial-time self-maximizing dominating shares
-- statement:
--   For every $n\ge2$, there is a share for additive valuations over goods that is feasible, self-maximizing, polynomial-time computable, and $\frac{2n}{3n-1}$-dominates every feasible share. The same share is $\frac45$-dominating when $n\le4$. For two agents and every $0<\varepsilon\le1$, there is such a share that is $(1-\varepsilon)$-dominating.
--
--   The theorem states scaled domination against every feasible share, not only an approximation to MMS.
--
--   Differences from the source:
--   - encoding: a share for each fixed agent count over arbitrary finite item names → for each `n ≥ 2`, a family `s m` on items `Fin m`, with `IsShareAt`, `FeasibleAt`, and `SelfMaxAt` for every m; reason: Section 6.1 treats a fixed-n share as a family over item counts, and name independence removes item names
--   - encoding: polynomial-time computable on finitely encoded additive values → for each fixed n, one Cook Turing machine on self-delimiting binary encodings of nonnegative rational item values; reason: these are the finite inputs whose bit length p.21 counts, and the mathematical share clauses still cover every real additive valuation
--   - encoding: rho-dominating feasible share → the share is feasible and its value is at least rho times every feasible competing share, pointwise; reason: this is the definition on p.5, written without shorthand
--   - encoding: every positive epsilon in the standing domain rho ≥ 0 → `0 < ε ≤ 1`; reason: the paper defines rho-domination only for nonnegative rho, so rho = 1-ε makes the upper bound implicit and excludes only an undefined use of the shorthand
-- source:
--   Babaioff & Feige, arXiv:2205.07519v1, Theorem 3, p.6

import Mathlib
import Definitions.Def_FairShares_IsAdditive
import Definitions.Def_FairShares_IsShareAt
import Definitions.Def_FairShares_FeasibleAt
import Definitions.Def_FairShares_SelfMaxAt
import Definitions.Def_CookPvsNP_defs

set_option autoImplicit false

namespace FairShares.Supplement

/-- **Theorem 3: polynomial-time self-maximizing dominating shares.**
Babaioff & Feige, *Fair Shares: Feasibility, Domination and Incentives*,
arXiv:2205.07519v1, Theorem 3, p.6.

For every `n ≥ 2`, there is an additive-goods share that is feasible, self-maximizing,
polynomial-time computable, and `2n/(3n-1)`-dominates every feasible additive-goods share; the
same share is `4/5`-dominating when `n ≤ 4`.  For two agents and every `0 < ε ≤ 1`, a
(possibly different) such share is `(1-ε)`-dominating.

**Formalization Note.** A share at agent count `n` is a family over every item count `m`, as the
paper explicitly permits in Section 6.1.  The machine may depend on the fixed `n`, and the
two-agent PTAS machine may depend on fixed `ε`.  The bound `ε ≤ 1` makes explicit the standing
domain `ρ ≥ 0` of `ρ`-domination from p.5.  Inputs are explicit binary encodings of nonnegative
rational item values.  Scaled domination is stated against every feasible share, not merely as
an MMS approximation. -/
theorem theorem_3 :
    let encNat : ℕ → List Bool := fun a =>
      (Nat.bits a).flatMap (fun b => [false, b]) ++ [true, true]
    let encInt : ℤ → List Bool := fun z => [decide (z < 0)] ++ encNat z.natAbs
    let encRat : ℚ → List Bool := fun r => encInt r.num ++ encNat r.den
    (∀ n : ℕ, 2 ≤ n →
      ∃ (s : (m : ℕ) → (Finset (Fin m) → ℝ) → ℝ)
          (run : List Bool → List Bool),
        (∀ m, FairShares.IsShareAt {v | FairShares.IsAdditive v} (s m)) ∧
        (∀ m, FairShares.FeasibleAt n {v | FairShares.IsAdditive v} (s m)) ∧
        (∀ m, FairShares.SelfMaxAt {v | FairShares.IsAdditive v} (s m)) ∧
        (∀ s' : (m : ℕ) → (Finset (Fin m) → ℝ) → ℝ,
          (∀ m, FairShares.IsShareAt {v | FairShares.IsAdditive v} (s' m)) →
          (∀ m, FairShares.FeasibleAt n {v | FairShares.IsAdditive v} (s' m)) →
          ∀ (m : ℕ) (v : Finset (Fin m) → ℝ), FairShares.IsAdditive v →
            ((2 * (n : ℝ)) / (3 * (n : ℝ) - 1)) * s' m v ≤ s m v) ∧
        (n ≤ 4 → ∀ s' : (m : ℕ) → (Finset (Fin m) → ℝ) → ℝ,
          (∀ m, FairShares.IsShareAt {v | FairShares.IsAdditive v} (s' m)) →
          (∀ m, FairShares.FeasibleAt n {v | FairShares.IsAdditive v} (s' m)) →
          ∀ (m : ℕ) (v : Finset (Fin m) → ℝ), FairShares.IsAdditive v →
            (4 / 5 : ℝ) * s' m v ≤ s m v) ∧
        CookPvsNP.PolyTimeComputable run ∧
        ∀ (m : ℕ) (w : Fin m → ℚ), (∀ g, 0 ≤ w g) →
          ∃ r : ℚ, (r : ℝ) = s m (fun S => ∑ g ∈ S, (w g : ℝ)) ∧
            run (encNat m ++ encNat n ++ (List.ofFn w).flatMap encRat) = encRat r) ∧
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ s : (m : ℕ) → (Finset (Fin m) → ℝ) → ℝ,
        (∀ m, FairShares.IsShareAt {v | FairShares.IsAdditive v} (s m)) ∧
        (∀ m, FairShares.FeasibleAt 2 {v | FairShares.IsAdditive v} (s m)) ∧
        (∀ m, FairShares.SelfMaxAt {v | FairShares.IsAdditive v} (s m)) ∧
        (∃ run : List Bool → List Bool, CookPvsNP.PolyTimeComputable run ∧
          ∀ (m : ℕ) (w : Fin m → ℚ), (∀ g, 0 ≤ w g) →
            ∃ r : ℚ, (r : ℝ) = s m (fun S => ∑ g ∈ S, (w g : ℝ)) ∧
              run (encNat m ++ encNat 2 ++ (List.ofFn w).flatMap encRat) = encRat r) ∧
        ∀ s' : (m : ℕ) → (Finset (Fin m) → ℝ) → ℝ,
          (∀ m, FairShares.IsShareAt {v | FairShares.IsAdditive v} (s' m)) →
          (∀ m, FairShares.FeasibleAt 2 {v | FairShares.IsAdditive v} (s' m)) →
          ∀ (m : ℕ) (v : Finset (Fin m) → ℝ), FairShares.IsAdditive v →
            (1 - ε) * s' m v ≤ s m v) := by sorry

end FairShares.Supplement
