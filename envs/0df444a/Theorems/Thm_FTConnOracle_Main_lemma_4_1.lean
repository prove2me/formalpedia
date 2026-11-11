-- Prove2me | Theorems.Thm_FTConnOracle_Main_lemma_4_1
-- name    : FTConnOracle.Main.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:32:34.98745+00:00
-- url     : https://prove2.me/theorems/f32c7120-5045-4988-a573-879b27fbd729
-- title:
--   Lemma 4.1 — bipartite expanders with r = O(t log 2n), 1 ≤ ℓ = O(log 2n) and (4.1); in polynomial time with an extra n^{o(1)}
-- statement:
--   There is a universal constant $C>0$ such that for every $n\ge2$ and every integer $1\le t<n/4$ there is a bipartite graph $B$ with left side $[n]$ and right side $[r]$, all of whose left vertices have the same degree $\ell$, with
--
--   $$r\le C\,t\log(2n),\qquad 1\le\ell\le C\log(2n),\qquad |\Gamma(U)|\ge\tfrac34\,\ell\,|U|\ \text{ for every }U\subseteq[n],\ |U|\le2t.\qquad(4.1)$$
--
--   Moreover (polynomial-time version), there are $C>0$, a function $h:\mathbb N\to\mathbb R$ with $h(n)\to0$, and one polynomial-time machine that on input $(1^n,1^t)$ outputs the incidence code of such a $B$ (left-regular of degree $\ell\ge1$, satisfying (4.1)) with
--
--   $$r\le C\,t\log(2n)\cdot n^{h(n)},\qquad \ell\le C\log(2n)\cdot n^{h(n)},$$
--
--   for every $n\ge2$ and integer $1\le t<n/4$.
--
--   These lossless expanders define the sketches of both oracles; the second sentence is what makes the encoders polynomial-time in Theorem 1.1.
--
--   **Formalization Note.** Logarithms are natural; the base only changes $C$.
--
--   Differences from the source:
--   - encoding: r = O(t log(2n)), ℓ = O(log(2n)) → one universal C > 0, quantified before n and t: r ≤ C·t·log(2n), ℓ ≤ C·log(2n); reason: standard meaning of O(·) with absolute constants
--   - reading: If one insists on polynomial in n time computation of B, then ℓ, r grow by a factor of n^{o(1)} → one polynomial-time machine (LowErrExt.IsPolyTime) maps (1^n, 1^t) to incidenceCode B for a left-regular B with ℓ ≥ 1 and (4.1), r ≤ C·t·log(2n)·n^{h(n)}, ℓ ≤ C·log(2n)·n^{h(n)}, with one h → 0 fixed before n and t; reason: 'polynomial in n time' read as one uniform algorithm; the input (1^n, 1^t) has length Θ(n), so polynomial in the input length is polynomial in n; n^{o(1)} read as n^{h(n)} with h → 0
-- source:
--   Parter, Tzalik, Deterministic Fault-Tolerant Connectivity Oracles with Subqadratic Space, STOC 2027 submission (manuscript sha256 168306b7…), p. 16 (PDF 18), Lemma 4.1 (4.1)

import Mathlib
import Definitions.Def_FTConnOracle_Main_Expander
import Definitions.Def_FTConnOracle_Main_Codes
import Definitions.Def_LowErrExt_IsPolyTime

open Filter Topology

namespace FTConnOracle.Main

/-- Lemma 4.1 (p. 16), both sentences. (1) There is a universal `C > 0` such that for every
`n ≥ 2` and integer `1 ≤ t < n/4` there is a bipartite graph `B` with left side `[n]` and right
side `[r]`, `r ≤ C t log(2n)`, all left degrees equal to `ℓ` with `1 ≤ ℓ ≤ C log(2n)`, satisfying
(4.1) for every `U ⊆ [n]` with `|U| ≤ 2t`. (2) Polynomial-time version: one polynomial-time
machine maps `(n, t)` (in unary) to the incidence code of such a `B` whose `ℓ` and `r` are larger
by at most a factor `n^{h(n)}`, `h(n) → 0`. -/
theorem lemma_4_1 :
    (∃ C : ℝ, 0 < C ∧
      ∀ n t : ℕ, 2 ≤ n → 1 ≤ t → (t : ℝ) < (n : ℝ) / 4 →
        ∃ (r ℓ : ℕ) (B : Fin n → Finset (Fin r)),
          (r : ℝ) ≤ C * (t : ℝ) * Real.log (2 * (n : ℝ)) ∧
          1 ≤ ℓ ∧ (ℓ : ℝ) ≤ C * Real.log (2 * (n : ℝ)) ∧
          IsLeftRegular B ℓ ∧ HasExpansion B ℓ t) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ h : ℕ → ℝ, Tendsto h atTop (𝓝 0) ∧
      ∃ A : List (List Bool) → List Bool, LowErrExt.IsPolyTime A ∧
        ∀ n t : ℕ, 2 ≤ n → 1 ≤ t → (t : ℝ) < (n : ℝ) / 4 →
          ∃ (r ℓ : ℕ) (B : Fin n → Finset (Fin r)),
            A (expanderInput n t) = incidenceCode B ∧
            (r : ℝ) ≤ C * (t : ℝ) * Real.log (2 * (n : ℝ)) * (n : ℝ) ^ h n ∧
            1 ≤ ℓ ∧ (ℓ : ℝ) ≤ C * Real.log (2 * (n : ℝ)) * (n : ℝ) ^ h n ∧
            IsLeftRegular B ℓ ∧ HasExpansion B ℓ t) := by sorry

end FTConnOracle.Main
