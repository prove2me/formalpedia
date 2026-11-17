-- Prove2me | Theorems.Thm_ApproxDegComp_Supplement_theorem_32
-- name    : ApproxDegComp.Supplement.theorem_32
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:02:30.283967+00:00
-- url     : https://prove2.me/theorems/59cedbb1-8cc8-476e-aa06-594269d18a7d
-- title:
--   Theorem 32 — $Q_E(f\circ\mathrm{OR}_m)=O(m\deg(f)+n^2\sqrt m)$
-- statement:
--   **An exact quantum algorithm for $f\circ\mathrm{OR}_m$.** There is an absolute constant $C>0$ such that for all $n,m\ge0$ and every Boolean function $f:\{0,1\}^n\to\{0,1\}$ of (exact) degree $d=\deg(f)$,
--
--   $$Q_E(f\circ\mathrm{OR}_m)\ \le\ C\big(m\,d+n^2\sqrt m\big).$$
--
--   Here $\deg(f)$ is the least total degree of a real polynomial equal to $f$ on $\{0,1\}^n$ (the $0$-approximate degree), $f\circ\mathrm{OR}_m$ is the block composition on $nm$ bits, and $Q_E$ is the exact quantum query complexity: the least number of oracle calls of a quantum query algorithm that outputs the correct value with probability $1$ on every input.
--
--   The bound is the upper half of the paper's counterexample: when $m$ is large compared with $n$ but $d$ is small compared with $Q_E(f)$, it beats $Q_E(f)\,Q_E(\mathrm{OR}_m)=Q_E(f)\,m$ (Theorem 33).
--
--   Differences from the source:
--
--   - encoding: O(·) → one absolute constant C > 0 quantified before n, m, f, the bound holding for all n, m ≥ 0; reason: the standard reading of the asymptotic notation, uniform in every parameter
--   - encoding: "degree d" of f → approxDegEps 0 f, the base mission's 0-approximate degree; reason: Definition 2 of the source: for ϵ = 0 it is the exact degree
--   - encoding: f ∘ OR_m and Q_E → OAI.Paper320.compose f (orFn m) and QE (QAlgorithms.QueryAlg with query register Option (Fin n × Fin m) × Bool, any finite workspace, any fixed unit start state); reason: Lean representation of Definitions 1, 12–14, same quantities
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Theorem 32, p.34 (Definitions 2, 12–14, pp.11, 13)

import Mathlib
import Definitions.Def_ApproxDegComp_approxDeg
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition
import Definitions.Def_ApproxDegComp_Supplement_orFn
import Definitions.Def_ApproxDegComp_Supplement_QE

namespace ApproxDegComp

namespace Supplement

/-- **Theorem 32**, p.34 (proof pp.34–37).
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Theorem 32, p.34: "For every Boolean function f : {0,1}ⁿ → {0,1}
of degree d, Q_E(f ∘ OR_m) = O(md + n²√m)."

**Formalization Note** `O(·)` is one absolute constant `C`, chosen before `n`, `m` and `f`; the
bound is stated for all `n, m` at once. The degree `d` of `f` is its exact degree, the base
mission's `approxDegEps 0 f` (Definition 2: "When ϵ = 0, it is the exact degree of f").
`f ∘ OR_m` is the block composition `OAI.Paper320.compose f (orFn m)` on `Fin n × Fin m`, a total
function. `Q_E` is exact quantum query complexity (Definitions 12–14), counting oracle calls only. -/
theorem theorem_32 : ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (f : (Fin n → Bool) → Bool),
    (QE (OAI.Paper320.compose f (orFn m)) : ℝ) ≤
      C * ((m : ℝ) * (approxDegEps 0 f : ℝ) + (n : ℝ) ^ 2 * Real.sqrt (m : ℝ)) := by sorry

end Supplement

end ApproxDegComp
