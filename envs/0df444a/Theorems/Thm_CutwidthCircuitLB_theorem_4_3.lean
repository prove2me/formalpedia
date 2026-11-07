-- Prove2me | Theorems.Thm_CutwidthCircuitLB_theorem_4_3
-- name    : CutwidthCircuitLB.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:28:58.723539+00:00
-- url     : https://prove2.me/theorems/bcad91c9-798c-4286-b52b-2264cd5879b3
-- title:
--   Theorem 4.3 — cubic cutwidth constant $\le \alpha$ implies a $(1 + 1/\alpha - \varepsilon)n$ circuit lower bound
-- statement:
--   Suppose the cubic cutwidth constant is at most $\alpha$, and let $F_n$ be a family with the sumset property of Theorem 1.6 with exponent $c > 1$ (such as Li's function). Then for all $\varepsilon > 0$ and all large enough $n$, every $B_2$-circuit computing $F_n$ has more than
--   $$
--   \Big(1 + \frac1\alpha - \varepsilon\Big) n
--   $$
--   gates.
--
--   This is the generic connection between cutwidth upper bounds and circuit lower bounds; with $\alpha = 2\kappa_E$ it gives the main theorem.
--
--   **Formalization Note** The theorem is stated for every family with the sumset property, not only for Li's function. The threshold for $n$ may depend on $\alpha$, $c$, $F$ and $\varepsilon$.
--
--   Differences from the source:
--   - generalization: Li's function F_n with the constant c > 1 of Theorem 1.6 → every c > 1 and every family F with SumsetBalanced c F; reason: the proof uses only Theorem 1.6's property; Li's function with its constant is an instance
--   - encoding: (1 + 1/α − ε)n with α the bound on the cubic cutwidth constant (α implicitly positive) → hypothesis 0 < α; reason: 1/α needs α ≠ 0, and the cutwidth hypothesis fails for α ≤ 0 (cubic graphs have linear cutwidth), so no instance with content is excluded
--   - reading: the cubic cutwidth constant (an infimum over admissible β > 0) is at most α → CubicCutwidthAtMost α: every β > α admits r = o(N) with cw ≤ β(M − N) + r(N); reason: the admissible set is upward closed (M − N ≥ −1 for connected graphs), so this is equivalent to the infimum being at most α; r(N) < o(N) read as r = o(N)
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Theorem 4.3, p.12

import Mathlib
import Definitions.Def_CutwidthCircuitLB_B2Circuit
import Definitions.Def_CutwidthCircuitLB_B2Circuit_prefixValues
import Definitions.Def_CutwidthCircuitLB_B2Circuit_eval
import Definitions.Def_CutwidthCircuitLB_B2Circuit_Computes
import Definitions.Def_CutwidthCircuitLB_SumsetBalanced
import Definitions.Def_CombOpt_MatchingPolytope_Graph
import Definitions.Def_CombOpt_MatchingPolytope_Graph_IsLoopless
import Definitions.Def_CutwidthCircuitLB_IsSubcubic
import Definitions.Def_CutwidthCircuitLB_IsConnected
import Definitions.Def_CutwidthCircuitLB_edgeMultiset
import Definitions.Def_CutwidthCircuitLB_cutSize
import Definitions.Def_CutwidthCircuitLB_CutwidthLE
import Definitions.Def_CutwidthCircuitLB_CubicCutwidthAtMost

namespace CutwidthCircuitLB

/-- **Theorem 4.3** (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), Theorem 4.3, p.12): suppose the cubic cutwidth constant is at most `α`.
Then for all `ε > 0` and all large enough `n`, every B₂-circuit computing Li's function `Fₙ`
(Theorem 1.6) has more than `(1 + 1/α − ε)n` gates.

**Formalization Note** Stated for every family `F` with the sumset property of Theorem 1.6
(exponent `c > 1`), which is the only property of Li's function the proof uses; `0 < α` as in
Lemma 3.1. -/
theorem theorem_4_3 (α : ℝ) (hα : 0 < α) (hcw : CubicCutwidthAtMost α) (c : ℝ) (hc : 1 < c)
    (F : (n : ℕ) → (Fin n → Bool) → Bool) (hF : SumsetBalanced c F) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ C : B2Circuit n, C.Computes (F n) →
      (1 + 1 / α - ε) * (n : ℝ) < (C.size : ℝ) := by sorry

end CutwidthCircuitLB
