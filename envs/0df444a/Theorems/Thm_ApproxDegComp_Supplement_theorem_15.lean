-- Prove2me | Theorems.Thm_ApproxDegComp_Supplement_theorem_15
-- name    : ApproxDegComp.Supplement.theorem_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:00:42.38596+00:00
-- url     : https://prove2.me/theorems/66b5dc13-8126-478b-b89a-daf26f15a8aa
-- title:
--   Theorem 15 — $\widetilde{\deg}(f\circ\mathrm{OR}_m)=\Omega\big(\widetilde{\deg}(f)\sqrt{m/\log 2n}\big)$
-- statement:
--   **Lower bound for $f$ composed with OR.** There is an absolute constant $c>0$ such that for every $n\ge0$, every $m\ge1$ and every Boolean function $f:\{0,1\}^n\to\{0,1\}$,
--
--   $$\widetilde{\deg}(f\circ\mathrm{OR}_m)\ \ge\ c\,\widetilde{\deg}(f)\sqrt{\frac{m}{\log 2n}} .$$
--
--   Here $\widetilde{\deg}$ is the ($1/3$-)approximate degree, $f\circ\mathrm{OR}_m$ is the block composition on $nm$ bits, $(f\circ\mathrm{OR}_m)(x^{(1)},\dots,x^{(n)})=f(\mathrm{OR}_m(x^{(1)}),\dots,\mathrm{OR}_m(x^{(n)}))$, and $\log$ is the natural logarithm.
--
--   Since $\widetilde{\deg}(\mathrm{OR}_m)=\Theta(\sqrt m)$, this is the composition theorem for the inner function OR up to a factor $\sqrt{\log 2n}$, for an arbitrary outer function. It is the warm-up of the paper's approximate-degree part.
--
--   **Formalization Note** The constant $c$ is chosen before $n$, $m$ and $f$. For $n=0$ Lean's conventions make the left factor $\sqrt{m/\log 0}=0$, so that case is trivial (as in the paper, where a function of no variables has approximate degree $0$).
--
--   Differences from the source:
--
--   - encoding: Ω(·) → one absolute constant c > 0 quantified before n, m, f; reason: the standard reading of the asymptotic notation, uniform in every parameter
--   - encoding: {0,1}ⁿ and the block composition f ∘ OR_m → Fin n → Bool and OAI.Paper320.compose f (orFn m) on Fin n × Fin m; reason: Lean representation, same functions
--   - encoding: log 2n → Real.log (2n), and at n = 0 the value √(m/log 0) is read as 0; reason: a change of base of the logarithm is absorbed by c, and the n = 0 case is undefined in the source and trivial (d̃eg(f) = 0) there
--   - reading: "Equivalently, d̃eg(f ∘ OR_m) ≥ Ω̃(d̃eg(f) d̃eg(OR_m))" → not stated separately; reason: the sentence restates the displayed bound through the cited d̃eg(OR_m) = Θ(√m) with an unspecified polylogarithmic factor; the displayed bound, stated here, implies it
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Theorem 15, p.18

import Mathlib
import Definitions.Def_ApproxDegComp_approxDeg
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition
import Definitions.Def_ApproxDegComp_Supplement_orFn

namespace ApproxDegComp

namespace Supplement

/-- **Theorem 15 (Lower bound for f composed with OR)**, p.18.
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Theorem 15, p.18: "Let f : {0,1}ⁿ → {0,1} be an arbitrary
Boolean function. Then for every m ≥ 1, d̃eg(f ∘ OR_m) ≥ Ω(d̃eg(f) √(m / log 2n))."

**Formalization Note** `Ω(·)` is one absolute constant `c > 0`, chosen before `n`, `m` and `f`.
`f ∘ OR_m` is the block composition `OAI.Paper320.compose f (orFn m)` on `Fin n × Fin m`
(coordinate `(i, j)` is bit `j` of block `i`). `log` is the natural logarithm `Real.log` (a change
of base is absorbed by `c`). At `n = 0` Lean reads `m / log 0` as `0`, so that case holds trivially,
as it does in the paper (`d̃eg(f) = 0` for a function of no variables). The paper's restatement
"Equivalently, d̃eg(f ∘ OR_m) ≥ Ω̃(d̃eg(f) d̃eg(OR_m))" rests on the cited `d̃eg(OR_m) = Θ(√m)`
with an unspecified polylogarithmic factor and is not stated separately. -/
theorem theorem_15 : ∃ c : ℝ, 0 < c ∧ ∀ (n m : ℕ) (f : (Fin n → Bool) → Bool), 1 ≤ m →
    c * (approxDeg f : ℝ) * Real.sqrt ((m : ℝ) / Real.log (2 * (n : ℝ))) ≤
      (approxDeg (OAI.Paper320.compose f (orFn m)) : ℝ) := by sorry

end Supplement

end ApproxDegComp
