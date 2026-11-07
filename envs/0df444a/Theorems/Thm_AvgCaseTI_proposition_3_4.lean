-- Prove2me | Theorems.Thm_AvgCaseTI_proposition_3_4
-- name    : AvgCaseTI.proposition_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:42:38.707387+00:00
-- url     : https://prove2.me/theorems/566b7bbb-3fda-4eda-84da-46e4103e2153
-- title:
--   Proposition 3.4 — the one-dimensional hull is a uniform self-dual line
-- statement:
--   Let $n\ge2$, $\mathbb F_q$ a finite field, and $\mathcal A$ a uniformly random $n$-dimensional subspace of $\mathrm M(n,q)$, conditioned on $\dim H(\mathcal A)=1$. Then the hull $H(\mathcal A)$ is uniformly distributed among the self-dual lines, except that $\mathrm{span}\{I_n\}$ is excluded when $q$ and $n$ are both even. Consequently, a uniformly chosen nonzero generator of the hull is uniform among the nonzero self-dual matrices, with all scalar matrices excluded when $q$ and $n$ are both even. Precisely:
--   1. every one-dimensional hull of an $n$-dimensional code is a self-dual line;
--   2. if $q$ and $n$ are both even, no $n$-dimensional code has hull $\mathrm{span}\{I_n\}$;
--   3. any two self-dual lines, neither equal to $\mathrm{span}\{I_n\}$ when $q,n$ are both even, are the hull of equally many $n$-dimensional codes;
--   4. any two nonzero self-dual matrices $X,X'$, neither scalar when $q,n$ are both even, lie in the one-dimensional hull of equally many $n$-dimensional codes.
--
--   The algorithm of Theorem 1.1 uses this to transfer the random-matrix estimate of Theorem 3.5 to the hull generator.
--
--   **Formalization Note** Uniformity is equality of counts. Clause 4 is the "consequently" statement: the probability that a uniform nonzero generator of the hull of a uniform hull-one code equals $X$ is proportional to the number of such codes whose hull contains $X$.
--
--   Differences from the source:
--
--   - encoding: "uniformly distributed among the self-dual lines, except …" and "a uniformly chosen nonzero generator … is uniform among …" → support clauses 1–2 and equal counts 3–4; reason: uniform distribution on a finite set is equality of counts on its support; the generator law is proportional to the count in clause 4
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Proposition 3.4, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_AvgCaseTI_hull

set_option autoImplicit false

namespace AvgCaseTI

/-- **Proposition 3.4 (the one-dimensional hull is a uniform allowed self-dual line).**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Proposition 3.4, p.17
(PDF p.19). Let `n ≥ 2` and let `𝒞` range over the `n`-dimensional subspaces of `M(n, q)`.
1. Every one-dimensional hull is a self-dual line.
2. If `q` and `n` are both even, no `𝒞` has hull `span{I_n}`.
3. Any two self-dual lines, neither of them `span{I_n}` when `q` and `n` are both even, are the hull
   of equally many `𝒞` (so, conditioned on `dim H(𝒞) = 1`, the hull is uniform among these lines).
4. Consequently: any two nonzero self-dual matrices `X, X'`, neither of them scalar when `q` and `n` are
   both even, lie in the (one-dimensional) hull of equally many `𝒞`; so a uniform nonzero generator of
   the hull is uniform among these matrices.

**Formalization Note.** Uniformity is equality of counts; "self-dual line" is `IsSelfDualLine`
(one-dimensional, `L ⊆ L^⊥`). -/
theorem proposition_3_4 {K : Type*} [Field K] [Fintype K] {q : ℕ} (hq : Fintype.card K = q)
    (n : ℕ) (hn : 2 ≤ n) :
    (∀ C : Submodule K (Mat K n), Module.finrank K C = n → Module.finrank K (hull C) = 1 →
      IsSelfDualLine (hull C)) ∧
    (Even q → Even n → ∀ C : Submodule K (Mat K n), Module.finrank K C = n →
      hull C ≠ Submodule.span K {(1 : Mat K n)}) ∧
    (∀ L L' : Submodule K (Mat K n), IsSelfDualLine L → IsSelfDualLine L' →
      ¬ (Even q ∧ Even n ∧ L = Submodule.span K {(1 : Mat K n)}) →
      ¬ (Even q ∧ Even n ∧ L' = Submodule.span K {(1 : Mat K n)}) →
      Nat.card {C : Submodule K (Mat K n) // Module.finrank K C = n ∧ hull C = L} =
        Nat.card {C : Submodule K (Mat K n) // Module.finrank K C = n ∧ hull C = L'}) ∧
    ∀ X X' : Mat K n, X ≠ 0 → SelfDual X → X' ≠ 0 → SelfDual X' →
      ¬ (Even q ∧ Even n ∧ ∃ a : K, X = a • (1 : Mat K n)) →
      ¬ (Even q ∧ Even n ∧ ∃ a : K, X' = a • (1 : Mat K n)) →
      Nat.card {C : Submodule K (Mat K n) //
          Module.finrank K C = n ∧ Module.finrank K (hull C) = 1 ∧ X ∈ hull C} =
        Nat.card {C : Submodule K (Mat K n) //
          Module.finrank K C = n ∧ Module.finrank K (hull C) = 1 ∧ X' ∈ hull C} := by sorry

end AvgCaseTI
