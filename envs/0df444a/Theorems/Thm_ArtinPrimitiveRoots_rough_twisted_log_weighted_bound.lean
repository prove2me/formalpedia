-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_rough_twisted_log_weighted_bound
-- name    : ArtinPrimitiveRoots.rough_twisted_log_weighted_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T12:54:07.579986+00:00
-- url     : https://prove2.me/theorems/89fdb99b-62d1-4254-b2df-db947ad96b96
-- title:
--   (10.19), proof of Proposition 10.3 (OpenAI) — bounds for the W-rough sum of χ(m) m^{iu}/log m, below and above T* = exp(L/(log L)²)
-- statement:
--   There is an absolute constant $C_3 > 0$ with the following property. Fix $0 < w_- < w_+ < 1$ and $A_0 > 0$, and write $L = \log x$, $W = \exp(L^{0.24})$ (`sieveLevel x`), $V(W) = \prod_{p \le W}(1 - 1/p)$ (`mertensProduct`) and $T_* = \exp(L/(\log L)^2)$. There are $C_0, c_0 > 0$ such that for every $A_4 > 0$ there are $K$ and $x_0$ such that for every $x \ge x_0$, every $M > 0$ with $w_- \le \log M/L$ and $\log(2M)/L \le w_+$, every Dirichlet character $\chi$ modulo $k$ with $1 \le k \le L^{A_0}$, every interval $I' \subseteq [M, 2M]$, and every real $u$ with $1 \le |u| < x^2$,
--
--   $$\Bigl|\frac{1}{MV(W)}\sum_{\substack{m \in I'\\ P^-(m) > W}} \frac{\chi(m)\,m^{iu}}{\log m}\Bigr| \le K\Bigl(L^{-A_4} + \begin{cases} L^{C_0}\bigl(|u|^{-1} + x^{-c_0}\bigr), & |u| \le T_*,\\ L^{C_0}\exp\bigl(-L/(\log L)^{C_3}\bigr), & |u| > T_*.\end{cases}\Bigr)$$
--
--   $C_0$ and $c_0$ depend on $w_\pm$ and $A_0$ but not on $A_4$; $K$ and $x_0$ also depend on $A_4$.
--
--   This is the paper's bound for the small-prime proxy in the proof of Proposition 10.3, without the proxy's multiplier. On $W$-rough $m$ the proxy coefficient `roughProxy` is $D_\gamma(w)/(LV(W)) = wD_\gamma(w)/(V(W)\log m)$ with $w = \log m/L$, and the paper restores the factor $wD_\gamma(w)$ afterwards by partial summation (p. 69). The paper takes the bound from the proof of Lemma 5.2 of OpenAI's *The Poisson–Dirichlet law for prime predecessors*, using its companion paper's logarithmic-phase estimate (published here as `log_phase_progression`) above $T_*$. Published as a step of that proof.
--
--   **Formalization note.** The setting is that of Proposition 10.3 with $M = H_m$ (p. 67), and $M > 0$. The paper's quantifier order is kept: $C_3$ is absolute, so it is chosen first; $C_0, c_0$ are "fixed after $A_0, \delta$", where $\delta$, the lower exponent of the dyad, is here $w_-$; and "$C_0$ does not grow with $A_4$", so $A_4$ comes after them. The two ranges overlap at $|u| = T_*$, which is assigned to the first. Characters are Mathlib's `DirichletCharacter ℂ k`, zero on nonunits; "every interval" is any order-connected set; "$k \le L^{A_0}$" is read as $1 \le k \le L^{A_0}$.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 69: “For the proxy, the proof of [21, Lemma 5.2] gives the following uniform estimate. Put $T_* = \exp(L/(\log L)^2)$. For every interval $I' \subseteq [M, 2M]$, and with arbitrary fixed $A_4$, it states $\Bigl|\frac{1}{MV(W)}\sum_{m \in I',\ P^-(m) > W}\frac{\chi(m)m^{iu}}{\log m}\Bigr| \ll L^{-A_4} + \begin{cases} L^{C_0}(|u|^{-1} + x^{-c_0}), & 1 \le |u| \le T_*,\\ L^{C_0}\exp(-L/(\log L)^{C_3}), & T_* \le |u| < x^2.\end{cases}$ (10.19) Here $C_0, c_0 > 0$ are fixed after $A_0, \delta$, and $C_3 > 0$ is absolute; $C_0$ does not grow with $A_4$.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 69, proof of Proposition 10.3, (10.19)

import Mathlib
import Definitions.Def_ArtinSieve

namespace ArtinPrimitiveRoots

open Real

open Classical in
theorem rough_twisted_log_weighted_bound :
    ∃ C₃ : ℝ, 0 < C₃ ∧
    ∀ wMinus wPlus : ℝ, 0 < wMinus → wMinus < wPlus → wPlus < 1 →
    ∀ A₀ : ℝ, 0 < A₀ → ∃ C₀ c₀ : ℝ, 0 < C₀ ∧ 0 < c₀ ∧
    ∀ A₄ : ℝ, 0 < A₄ → ∃ K x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ M : ℝ, 0 < M → wMinus ≤ log M / log x → log (2 * M) / log x ≤ wPlus →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ log x ^ A₀ → ∀ χ : DirichletCharacter ℂ k,
      ∀ J : Set ℝ, J.OrdConnected → J ⊆ Set.Icc M (2 * M) →
      ∀ u : ℝ, 1 ≤ |u| → |u| < x ^ 2 →
        ‖((1 / (M * mertensProduct (sieveLevel x)) : ℝ) : ℂ) *
            ∑ m ∈ Finset.range (⌊2 * M⌋₊ + 1),
              (if (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m then
                χ (m : ZMod k) * (m : ℂ) ^ (Complex.I * u) / ((log m : ℝ) : ℂ) else 0)‖ ≤
          K * (log x ^ (-A₄) +
            if |u| ≤ exp (log x / log (log x) ^ 2) then
              log x ^ C₀ * (|u|⁻¹ + x ^ (-c₀))
            else log x ^ C₀ * exp (-(log x / log (log x) ^ C₃))) := by
  sorry

end ArtinPrimitiveRoots
