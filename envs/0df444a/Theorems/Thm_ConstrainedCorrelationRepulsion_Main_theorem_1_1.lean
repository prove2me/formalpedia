-- Prove2me | Theorems.Thm_ConstrainedCorrelationRepulsion_Main_theorem_1_1
-- name    : ConstrainedCorrelationRepulsion.Main.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:27:06.709147+00:00
-- url     : https://prove2.me/theorems/e48a4ee2-0ee9-4aec-b557-730a7a649b7a
-- title:
--   Theorem 1.1 — randomized (2 + ε)-approximation with uniform running time
-- statement:
--   For every fixed real $\varepsilon>0$, there is one finite randomized program that, on every feasible $n$-vertex complete unweighted constrained correlation clustering instance, returns a feasible partition and satisfies
--
--   $$
--   \mathbb E[\mathrm{cost}_I(P)]\le(2+\varepsilon)\mathrm{OPT}(I),\qquad \mathrm{time}\le(n/\varepsilon)^{O(\varepsilon^{-2})}.
--   $$
--
--   Both hard constraint types, all supported outputs, the original vertex count, and the computational bound are part of the conclusion. Input feasibility supplies no optimizer or good-output law. The universal exponent constants precede the accuracy, program and instance quantifiers.
--
--   **Formalization Note.** Use a rational internal tolerance $0<\varepsilon_c\le1$ within the requested accuracy, $A_0=60007$, $r=2\lceil256A_0^2/\varepsilon_c^2\rceil$, $\tau=\varepsilon_c/4$, and $T=n\lceil\log_2(n^2/\tau)\rceil$. Sampling and truncation each spend at most $\varepsilon_c\mathrm{OPT}/4$, leaving half the core slack for bounded fair-coin sampling implementations. The operational bit-cost conclusion permits only fair random bits. The final transfer uses core accuracy $\varepsilon/2$ and reduction slack $\varepsilon/2$. Expanded and original vertex counts are distinct.
--
--   Differences from the source:
--   - encoding: finite vertex set and partitions → Fin n with vertex-label partitions and unordered-pair cost; reason: every finite partition admits these labels, including n = 0; each pair is counted once
--   - reading: polynomial-time algorithm without a named machine → one finite charged register program, with fair random bits in rational bit-cost executions and exact-real arithmetic/Bernoulli(p) access for real inputs; reason: this makes the implicit computational model explicit without admitting optimization instructions or semantic callbacks
--   - encoding: the conventional (n/epsilon)^{O(epsilon^{-2})} bound for 0 < epsilon ≤ 1 → resourceBound C k epsilon n with max(2,n), min(epsilon,1), and positive universal natural C,k; reason: the proof handles empty inputs directly and uses accuracy one for epsilon > 1; the explicit bound is equivalent in the asymptotic regime
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), Theorem 1.1, printed p.1 (PDF p.2), proof printed pp.34–35 (PDF pp.35–36)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Algorithm

namespace ConstrainedCorrelationRepulsion.Main

open Classical MeasureTheory
open scoped BigOperators ENNReal

theorem theorem_1_1 :
  ∃ C k : ℕ, 0 < C ∧ 0 < k ∧ ∀ epsilon : ℝ, 0 < epsilon →
    ∃ code : Program, ∀ n (I : Instance n), FeasibleInput I →
      Approximates code I (2 + epsilon) (resourceBound C k epsilon n) := by sorry

end ConstrainedCorrelationRepulsion.Main
