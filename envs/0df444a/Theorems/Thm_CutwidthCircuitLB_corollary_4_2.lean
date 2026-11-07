-- Prove2me | Theorems.Thm_CutwidthCircuitLB_corollary_4_2
-- name    : CutwidthCircuitLB.corollary_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:29:23.720456+00:00
-- url     : https://prove2.me/theorems/5f54b1ab-8ffb-47eb-b7f8-af8151b8ef15
-- title:
--   Corollary 4.2 — properties of $F_n$ and the $2^{n-2}/n^{2c}$ edge bound
-- statement:
--   Let $c > 1$ and let $F_n : \{0,1\}^n \to \{0,1\}$ be a family with the sumset property of Theorem 1.6 with exponent $c$. For all sufficiently large $n$:
--   1. $|F_n^{-1}(1)| \ge 2^{n-2}$;
--   2. $F_n$ is an $n^c$-rectangle disperser;
--   3. $F_n$ depends on all but at most $c \log n + 1$ of its variables.
--
--   Consequently, every read-once program computing $F_n$ has at least
--   $$
--   \frac{2^{n-2}}{n^{2c}} = 2^{n - O(\log n)}
--   $$
--   edges. Logarithms are base $2$.
--
--   This is the branching-program lower bound (Lemma 1.2) for the explicit function; item 3 is what lets Theorem 4.3 discard the few unread variables of a circuit.
--
--   **Formalization Note** The statement is for every family with the sumset property; the paper's $F_n$ is Li's function from Theorem 1.6. All four conclusions hold for the same threshold $N$. Powers are real powers.
--
--   Differences from the source:
--   - generalization: Li's function F_n with the constant c > 1 of Theorem 1.6 → every c > 1 and every family F with SumsetBalanced c F; reason: the proof uses only Theorem 1.6's property; Li's function with its constant is an instance
--   - reading: every read-once program computing F_n has at least 2^{n−2}/n^{2c} = 2^{n−O(log n)} edges → numEdges ≥ 2^{n−2}/n^{2c}; reason: the O-form is notation for the explicit bound printed first
--   - encoding: 2^{n−2}, n^c, c log n → real powers (2:ℝ)^((n:ℝ) − 2), (n:ℝ)^c and Real.logb 2; reason: avoids natural-number subtraction; the paper's logarithms are base 2 (p.6)
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Corollary 4.2, p.11

import Mathlib
import Definitions.Def_CutwidthCircuitLB_ROBP
import Definitions.Def_CutwidthCircuitLB_ROBP_IsConsistentSegment
import Definitions.Def_CutwidthCircuitLB_ROBP_IsAcceptingPath
import Definitions.Def_CutwidthCircuitLB_ROBP_Accepts
import Definitions.Def_CutwidthCircuitLB_ROBP_Computes
import Definitions.Def_CutwidthCircuitLB_ROBP_numEdges
import Definitions.Def_CutwidthCircuitLB_rect
import Definitions.Def_CutwidthCircuitLB_IsRectangleDisperser
import Definitions.Def_CutwidthCircuitLB_DependsOn
import Definitions.Def_CutwidthCircuitLB_SumsetBalanced

namespace CutwidthCircuitLB

/-- **Corollary 4.2** (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), Corollary 4.2, p.11): let `c > 1` and let `Fₙ` have the sumset property
of Theorem 1.6 with exponent `c`. For all sufficiently large `n`:
1. `|Fₙ⁻¹(1)| ≥ 2^(n−2)`;
2. `Fₙ` is an `n^c`-rectangle disperser;
3. `Fₙ` depends on all but at most `c log n + 1` of its variables;
and consequently every read-once program computing `Fₙ` has at least `2^(n−2)/n^(2c)` edges.

**Formalization Note** Stated for every family with the property of Theorem 1.6 (the paper's
`Fₙ` is Li's function, which has it); logarithms are base 2 and powers are real powers. -/
theorem corollary_4_2 (c : ℝ) (hc : 1 < c) (F : (n : ℕ) → (Fin n → Bool) → Bool)
    (hF : SumsetBalanced c F) :
    ∃ N : ℕ, ∀ n ≥ N,
      (2 : ℝ) ^ ((n : ℝ) - 2) ≤ (({x : Fin n → Bool | F n x = true}.ncard : ℕ) : ℝ) ∧
      IsRectangleDisperser ((n : ℝ) ^ c) (F n) ∧
      (({j : Fin n | ¬ DependsOn (F n) j}.ncard : ℕ) : ℝ) ≤ c * Real.logb 2 n + 1 ∧
      ∀ R : ROBP n, R.Computes (F n) →
        (2 : ℝ) ^ ((n : ℝ) - 2) / (n : ℝ) ^ (2 * c) ≤ (R.numEdges : ℝ) := by sorry

end CutwidthCircuitLB
