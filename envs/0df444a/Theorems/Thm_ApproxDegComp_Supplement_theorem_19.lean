-- Prove2me | Theorems.Thm_ApproxDegComp_Supplement_theorem_19
-- name    : ApproxDegComp.Supplement.theorem_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:01:18.197196+00:00
-- url     : https://prove2.me/theorems/9cbc5aa2-875b-4cbe-b874-9f73f02b30b1
-- title:
--   Theorem 19 — $\widetilde{\mathrm{bdeg}}(f\circ\mathrm{PrTH}^t_m)=\Omega\big(\widetilde{\deg}(f)\,\widetilde{\mathrm{bdeg}}(\mathrm{PrTH}^t_m)\big)$
-- statement:
--   **Lower bound for inner threshold.** There is an absolute constant $c>0$ such that for all integers $n\ge0$ and $1\le t\le m$ and every non-constant Boolean function $f:\{0,1\}^n\to\{0,1\}$,
--
--   $$\widetilde{\mathrm{bdeg}}\big(f\circ\mathrm{PrTH}^t_m\big)\ \ge\ c\,\widetilde{\deg}(f)\,\widetilde{\mathrm{bdeg}}\big(\mathrm{PrTH}^t_m\big).$$
--
--   Here $\mathrm{PrTH}^t_m$ is the promise threshold function ($1$ on Hamming weight $t$, $0$ on weight $t-1$, undefined otherwise), and $f\circ\mathrm{PrTH}^t_m$ is the block composition of a total outer function with a partial inner one. It is defined on the inputs $(x^{(1)},\dots,x^{(n)})\in(\{0,1\}^m)^n$ every block of which has weight $t-1$ or $t$, with value $f(\mathrm{PrTH}^t_m(x^{(1)}),\dots,\mathrm{PrTH}^t_m(x^{(n)}))$. $\widetilde{\deg}$ is the approximate degree and $\widetilde{\mathrm{bdeg}}$ the bounded approximate degree: the approximating polynomial must lie in $[0,1]$ on the whole cube $\{0,1\}^{mn}$ and be within $1/3$ of the function on its domain.
--
--   This is the composition theorem for a partial inner function, in the bounded measure. It is the second warm-up before the general Theorem 23.
--
--   Differences from the source:
--
--   - encoding: Ω(·) → one absolute constant c > 0 quantified before n, m, t, f; reason: the standard reading of the asymptotic notation, uniform in every parameter
--   - encoding: "non-constant" f and the block composition f ∘ PrTH^t_m of Definition 1 → ∃ x y, f x ≠ f y, and NoPerfectRandComp.PartialFn.comp (PartialFn.total f) (prTh m t); reason: Lean representation; the published composition has exactly Definition 1's domain (every block in Dom(PrTH), outer domain the whole cube)
--   - encoding: |x| = t − 1 → hamWt x + 1 = t; reason: avoids natural-number subtraction; same set for t ≥ 1, which the theorem assumes
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Theorem 19, p.20 (Definitions 1, 3, 16, pp.11–13)

import Mathlib
import Definitions.Def_ApproxDegComp_approxDeg
import Definitions.Def_NoPerfectRandComp_PartialFn
import Definitions.Def_ApproxDegComp_Supplement_prTh
import Definitions.Def_ApproxDegComp_Supplement_bdeg

namespace ApproxDegComp

namespace Supplement

/-- **Theorem 19 (Lower bound for inner threshold)**, p.20.
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Theorem 19, p.20: "For a non-constant arbitrary Boolean function
f, and 1 ≤ t ≤ m, b̃deg(f ∘ PrTH^t_m) ≥ Ω(d̃eg(f) b̃deg(PrTH^t_m)), where PrTH^t_m(x) = 0 if
|x| = t − 1; 1 if |x| = t; undefined, otherwise."

**Formalization Note** `Ω(·)` is one absolute constant `c > 0`, chosen before `n`, `m`, `t` and `f`.
`f : {0,1}ⁿ → {0,1}` is total (`Fin n → Bool`), non-constant means it takes both values, and
`d̃eg(f)` is the base mission's approximate degree. `f ∘ PrTH^t_m` is the block composition of
Definition 1 (p.11) for the total outer `f` and the partial inner `PrTH^t_m`, i.e. the published
`NoPerfectRandComp.PartialFn.comp`: its domain is the inputs on `Fin n × Fin m` each of whose
blocks has Hamming weight `t − 1` or `t`, and its value is `f` applied to the blocks' `PrTH`
values. `b̃deg` is the bounded approximate degree of Definition 3: the approximating polynomial
must lie in `[0, 1]` on the whole cube `{0,1}^{mn}` and be within `1/3` on the domain. -/
theorem theorem_19 : ∃ c : ℝ, 0 < c ∧ ∀ (n m t : ℕ) (f : (Fin n → Bool) → Bool),
    (∃ x y, f x ≠ f y) → 1 ≤ t → t ≤ m →
    c * (approxDeg f : ℝ) * (bdeg (prTh m t) : ℝ) ≤
      (bdeg ((NoPerfectRandComp.PartialFn.total f).comp (prTh m t)) : ℝ) := by sorry

end Supplement

end ApproxDegComp
