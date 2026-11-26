-- Prove2me | Theorems.Thm_BipHamCount_Deterministic_smallTerms_index_enumeration
-- name    : BipHamCount.Deterministic.smallTerms_index_enumeration
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:16:07.585346+00:00
-- url     : https://prove2.me/theorems/15f0717b-283b-54aa-b436-77096aa27b8e
-- title:
--   Small-term index enumeration: exact output and charged work
-- statement:
--   For the subset and three-way label routines used in Proposition 4.2, choosing $q$ indices returns exactly the length-$q$ sublists up to permutation. On a list of distinct indices, three-way labelling enumerates each ordered pair with the prescribed union exactly once. The charged work to enumerate a layer is polynomial per output, with an additive polynomial for empty layers. At the registered cutoff $k=\lfloor\alpha m\rfloor$, the weighted sum of layer sizes is at most $\exp(mH(\alpha))3^{\alpha m}$, where $H$ is binary entropy in nats.
-- source:
--   T. Koana and S. Kumabe, Counting Hamiltonian Cycles in Bipartite Digraphs Deterministically in O(1.9526^n) Time, §4.2, pp. 7–8, auxiliary enumeration and cost estimates for Proposition 4.2. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/814.pdf

import Mathlib
import Definitions.Def_BipHamCount_Deterministic_Programs
open scoped BigOperators

namespace BipHamCount.Deterministic

theorem smallTerms_index_enumeration :
    (∀ (m : ℕ) (xs : List (Fin m)) (q s : ℕ),
      ((chooseSets xs q).run s).1.Perm ((xs.sublistsLen q).map List.toFinset) ∧
      ((chooseSets xs q).run s).2 ≤ s + (m+4)*(3*(xs.length+1)*(xs.length.choose q)+1)) ∧
    (∀ (m : ℕ) (xs : List (Fin m)) (s : ℕ), xs.Nodup →
      ((labelPairs xs).run s).1.Nodup ∧
      (∀ t : Finset (Fin m) × Finset (Fin m),
        t ∈ ((labelPairs xs).run s).1 ↔ t.1 ∪ t.2 = xs.toFinset) ∧
      ((labelPairs xs).run s).1.length = 3^xs.length ∧
      ((labelPairs xs).run s).2 ≤ s+(4*m+12)*3^xs.length) ∧
    (∀ m : ℕ, (∑ q ∈ Finset.range (kOf m+1), (m.choose q : ℝ)*(3:ℝ)^q) ≤
      Real.exp ((m:ℝ)*Real.binEntropy alpha)*(3:ℝ)^(alpha*m)) := by sorry

end BipHamCount.Deterministic
