-- Prove2me | Theorems.Thm_CorrelatedLocalSearch_theorem_4_1_robustness
-- name    : CorrelatedLocalSearch.theorem_4_1_robustness
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:40:16.815886+00:00
-- url     : https://prove2.me/theorems/e3a62d57-aa70-4c0f-92da-c07268712374
-- title:
--   Theorem 4.1 — the promise-SAT walk under every source in $\mathcal Q_{s,D}$, $s\in[s_*,1]$: tail (9) and $\mathbb E_\nu\tau\le C\min\{L^3,L/\delta\}$ (10)
-- statement:
--   Fix integers $k/2<r<k$ and let $\lambda=\sqrt{r/(k-r)}$ and $s_*=\log_k(2\sqrt{r(k-r)})$. There are constants $c,C>0$, depending only on $k$ and $r$, such that the following holds. Let $\Phi$ be a strongly $r$-satisfiable $k$-CNF on $n$ variables with strong witness $x^*$, let $x_0$ be an initial assignment with $h=d_H(x_0,x^*)$, and run the walk with any valid deterministic nonanticipating clause selector, flipping at each step the variable of the literal indexed by the next symbol of a tape drawn from $\nu$. Put $L=h+\log D+1$ and $\delta=s-s_*$. Then for every $s\in[s_*,1]$, $D\ge1$, $\nu\in\mathcal Q_{s,D}$ and integer $T\ge0$,
--   $$
--   \mathbb P_\nu\{\tau>T\}\ \le\ \min\bigl\{1,\ CD\lambda^h e^{-cT^{1/3}},\ D\lambda^h k^{-\delta T}\bigr\},\tag{9}
--   $$
--   $$
--   \mathbb E_\nu\tau\ \le\ C\min\{L^3,\ L/\delta\},\tag{10}
--   $$
--   with $L/0=\infty$. Here $\tau$ counts variable flips until the formula is satisfied, and there is no restriction on clause overlap.
--
--   The bound depends on the distance to a strong witness and on the source parameters only, not on the number of variables: a single correlated tape with a prefix probability bound at or above the threshold $s_*$ suffices for the walk to terminate in polynomially many expected flips.
--
--   **Formalization Note** (10) is stated as two bounds, $\mathbb E_\nu\tau\le CL^3$ and, when $\delta>0$, $\mathbb E_\nu\tau\le CL/\delta$.
--
--   Differences from the source:
--   - encoding: integers k/2 < r < k → natural numbers k, r with k < 2r and r < k; reason: same instances
--   - encoding: constants c, C depending only on k, r → ∃ c C > 0 after k, r and before n, Φ, x∗, x₀, the selector, s, D, ν, T; reason: same quantifier order
--   - encoding: E_ν τ ≤ C min{L³, L/δ} with L/0 = ∞ → E_ν τ ≤ C L³ and (δ > 0 → E_ν τ ≤ C L/δ); reason: same bound
--   - encoding: any violated clause chosen by a deterministic nonanticipating selector → a selector List (Fin k) → (Fin n → Bool) → Clause k n returning a violated clause of Φ on every unsatisfying assignment; reason: a selector valid on reachable histories extends to one valid everywhere without changing any run
--   - encoding: τ, the number of flips until Φ is satisfied → walkTau ∈ ℕ∞, ⊤ if Φ is never satisfied; reason: same random variable
--   - encoding: E_ν τ → lower Lebesgue integral ∫⁻ of τ cast from ℕ∞ to ℝ≥0∞; reason: τ is measurable (each {τ > T} is a finite union of cylinders), so this is the expectation, with value ∞ when ν{τ = ∞} > 0
--   - encoding: log D (base not fixed) → natural logarithm Real.log; reason: another fixed base only rescales C
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), Theorem 4.1, eqs. (9)–(10), p.9 (PDF p.11)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_SourceClass
import Definitions.Def_CorrelatedLocalSearch_sStar
import Definitions.Def_CorrelatedLocalSearch_Clause
import Definitions.Def_CorrelatedLocalSearch_walkTau

set_option autoImplicit false

namespace CorrelatedLocalSearch

open MeasureTheory

/-- Theorem 4.1 (robustness from distance to a solution) (Xu, *Local Search with Correlated
Randomness*, arXiv:2607.17469 (sha256 17e00d69…), Theorem 4.1, eqs. (9)–(10), p.9). Fix
integers `k/2 < r < k` and `λ, s∗` of (8). There are constants `c, C > 0`, depending only on
`k, r`, such that for every `n`, every `k`-CNF `Φ` on `n` variables with a strong witness `x∗`,
every initial assignment `x₀` with `h = d_H(x₀, x∗)`, every deterministic nonanticipating valid
clause selector, every `s ∈ [s∗, 1]`, `D ≥ 1`, `ν ∈ Q_{s,D}` and integer `T ≥ 0`, with
`L = h + log D + 1` and `δ = s − s∗`,
`P_ν{τ > T} ≤ min{1, C D λ^h e^{−c T^{1/3}}, D λ^h k^{−δT}}`   (9)
and `E_ν τ ≤ C min{L³, L/δ}` (with `L/0 = ∞`)   (10).

**Formalization Note** (10) is the conjunction `E_ν τ ≤ C L³` and `δ > 0 → E_ν τ ≤ C L/δ`,
which is `C min{L³, L/δ}` with `L/0 = ∞`. `τ` is `walkTau`, valued in `ℕ∞` (`⊤` if the walk
never satisfies `Φ`); `E_ν τ` is the lower Lebesgue integral of `τ` cast to `ℝ≥0∞`. `log` is
the natural logarithm; `T^{1/3}` and `k^{−δT}` are `Real.rpow`. `ν {τ > T}` is the outer
measure of the set. -/
theorem theorem_4_1_robustness (k r : ℕ) (hk : k < 2 * r) (hr : r < k) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (n : ℕ) (Φ : List (Clause k n)) (xs : Fin n → Bool), IsStrongWitness r Φ xs →
        ∀ (x₀ : Fin n → Bool) (sel : Selector k n), IsValidSelector Φ sel →
          ∀ s : ℝ, sStar k r ≤ s → s ≤ 1 → ∀ D : ℝ, 1 ≤ D →
            ∀ ν : Measure (ℕ → Fin k), ν ∈ SourceClass k s D →
              (∀ T : ℕ, ν {ω | (T : ℕ∞) < walkTau Φ sel x₀ ω} ≤
                ENNReal.ofReal (min 1 (min
                  (C * D * lam k r ^ hammingDist x₀ xs * Real.exp (-c * (T : ℝ) ^ ((1 : ℝ) / 3)))
                  (D * lam k r ^ hammingDist x₀ xs * (k : ℝ) ^ (-((s - sStar k r) * T)))))) ∧
              ∫⁻ ω, ((walkTau Φ sel x₀ ω : ℕ∞) : ENNReal) ∂ν ≤
                ENNReal.ofReal (C * ((hammingDist x₀ xs : ℝ) + Real.log D + 1) ^ 3) ∧
              (0 < s - sStar k r →
                ∫⁻ ω, ((walkTau Φ sel x₀ ω : ℕ∞) : ENNReal) ∂ν ≤
                  ENNReal.ofReal (C * ((hammingDist x₀ xs : ℝ) + Real.log D + 1) /
                    (s - sStar k r))) := by sorry

end CorrelatedLocalSearch
