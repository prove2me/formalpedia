-- Prove2me | Theorems.Thm_BipHamCount_Deterministic_largeTerms_layer_enumeration
-- name    : BipHamCount.Deterministic.largeTerms_layer_enumeration
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:17:31.089149+00:00
-- url     : https://prove2.me/theorems/c40992ad-84b3-590f-91fe-0fc93e9b1159
-- title:
--   Large-term dynamic program: exact layer sizes and entropy bound
-- statement:
--   For layer $q$ of the large-term program, the two actual enumeration routines produce exactly $\binom{m-(k-q)_+}{q}\binom{m}{q}$ ordered row-column pairs. At the paper’s cutoff $k=\lfloor\alpha m\rfloor$, the total across layers is at most $(m+1)(\alpha/(1-\alpha))^2\exp(2mH(\alpha))$, with natural-log entropy. The statement includes the finite-size loss from taking the floor.
-- source:
--   T. Koana and S. Kumabe, Counting Hamiltonian Cycles in Bipartite Digraphs Deterministically in O(1.9526^n) Time, Section 4.1, pp. 6–7, state-count estimate in Proposition 4.1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/814.pdf

import Mathlib
import Definitions.Def_BipHamCount_Deterministic_Programs
open scoped BigOperators

namespace BipHamCount.Deterministic

theorem largeTerms_layer_enumeration :
    (∀ (m k q s₁ s₂ s₃ s₄ : ℕ),
      ((chooseSets ((suffix (m:=m) (k-q)).run s₁).1 q).run s₂).1.length *
      ((chooseSets ((suffix (m:=m) 0).run s₃).1 q).run s₄).1.length =
        (m-(k-q)).choose q * m.choose q) ∧
    (∀ m : ℕ,
      (∑ q ∈ Finset.range (m+1), (m.choose q:ℝ)*((m-(kOf m-q)).choose q:ℝ)) ≤
      ((m:ℝ)+1)*(alpha/(1-alpha))^2*Real.exp (2*m*Real.binEntropy alpha)) := by sorry

end BipHamCount.Deterministic
