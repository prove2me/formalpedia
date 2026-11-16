-- Prove2me | Theorems.Thm_FasterPrimeEnum_Supplement_theorem_4_24
-- name    : FasterPrimeEnum.Supplement.theorem_4_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:52:02.427508+00:00
-- url     : https://prove2.me/theorems/0ec7f8fd-2ea9-4f7a-8fa2-c3ae84062df0
-- title:
--   Theorem 4.24 — restricted products in time $R(n)<n\log n\cdot\exp((\log\log n)^{1/2+o(1)})$
-- statement:
--   There is a restricted product algorithm over $\mathbb F_2$ (computing $f\lhd g$ for $f\in\mathbb F_2[x]_{2n}$, $g\in\mathbb F_2[x^{-1}]_n$) whose smoothed cost satisfies
--
--   $$
--   R(n)<n\log n\cdot\exp\big((\log\log n)^{1/2+o(1)}\big),
--   $$
--
--   equivalently $R^*(n)<\exp((\log\log n)^{1/2+o(1)})$.
--
--   The factor $\exp((\log\log n)^{1/2+o(1)})$ grows more slowly than any positive power of $\log n$; this bound is what keeps the restricted-product step of the heuristic algorithm within $N(\log\log N)^{1+o(1)}$.
--
--   **Formalization Note** One algorithm and one $\varepsilon(n)\to0$, with the strict bound at every $n\ge1$; $R(n)=n\max(1,\log n)R^*(n)$ is the smoothed cost of p.27, and the logarithms of the bound are clipped.
--
--   Differences from the source:
--   - encoding: the standard multitape Turing model, time = number of steps (p.3) → the published PrimitiveMachine (deterministic, multitape, alphabet Option Bool, one read and one write or move per step) with RunsWithin / RunOutcome (a halted run within the time bound, with exactly the output on a designated tape); reason: each model simulates the other with a constant-factor loss in time, which the stated bounds absorb (a change of the O-constant or a shift of an o(1) exponent); an existential over the more restricted machine is the stronger statement
--   - encoding: polynomials in F₂[x]_n and vectors in F₂^K → functions Fin n → ZMod 2 and Fin K → ZMod 2, given to machines as bit arrays in index order (vecBits); an input of degree < n is an array of exactly n bits; reason: the paper represents polynomials by their coefficient arrays in the monomial basis (p.19); the worst case over inputs of degree < n is the worst case over n-bit arrays
--   - encoding: log x and log log x in complexity bounds → logU x = log max(x, 2) and logU (logU x); reason: the paper's convention (p.2): in complexity bounds log x should be read as log max(x, 2)
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), Theorem 4.24, p.27

import Mathlib
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Log
import Definitions.Def_FasterPrimeEnum_Supplement_RestrictedProductAlgorithm

set_option autoImplicit false

namespace FasterPrimeEnum

namespace Supplement

open ThreeSumApsp
open Filter Topology

/-- **Theorem 4.24** — D. Harvey, *Faster enumeration of primes*, arXiv:2606.22851 (held version,
sha256 7fc13f17…), p.27.

"There is a restricted product algorithm achieving R(n) < n log n · exp((log log n)^{1/2+o(1)}), or
equivalently R*(n) < exp((log log n)^{1/2+o(1)})."

**Formalization Note.** A restricted product algorithm (§4.4: a machine computing `f ⊲ g` for all
`f ∈ F₂[x]_{2n}`, `g ∈ F₂[x^{−1}]_n`, every `n ≥ 1`) and one `ε → 0` (the `o(1)`), such that the
smoothed cost `R(n) = n max(1, log n) R*(n)` of p.27 satisfies the strict bound at every `n ≥ 1`.
In the bound, `log n` and `log log n` are clipped (p.2): `logU u = log max(u, 2)`. -/
theorem theorem_4_24 :
    ∃ (RP : RestrictedProductAlgorithm) (ε : ℕ → ℝ),
      Tendsto ε atTop (𝓝 0) ∧
      ∀ n : ℕ, 1 ≤ n →
        RP.Rcost n < (n : ℝ) * logU (n : ℝ) * Real.exp (logU (logU (n : ℝ)) ^ (1 / 2 + ε n)) := by sorry

end Supplement

end FasterPrimeEnum
