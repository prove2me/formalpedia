-- Prove2me | Theorems.Thm_F3SubsetSum_proposition_4_13
-- name    : F3SubsetSum.proposition_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:30:38.370009+00:00
-- url     : https://prove2.me/theorems/1a5f6e11-8c75-42c0-8467-d8ba5333bc90
-- title:
--   Proposition 4.13 — a drift function $\gamma$ with $\int_0^H du/\gamma(u)\le 100n^2/D$
-- statement:
--   Let $q\ge3$ be prime, $3\le D\le n$ and $H=\dim R_D$. There is a function $\gamma$, nondecreasing and nonnegative on $[0,H]$, such that:
--
--   1. for every history $a_1,\dots,a_{t-1}\in\mathbb F_q^n$ with $h_{t-1}>0$, a uniform new sample $a_t$ gives
--   $$\mathbb E\Bigl[\min\Bigl\{\frac{X_t}{\gamma(h_{t-1})},1\Bigr\}\ \Big|\ \mathcal F_{t-1}\Bigr]\ge\frac13 ;$$
--   2. $\displaystyle\int_0^H\frac{du}{\gamma(u)}\le\frac{100n^2}{D}$.
--
--   Here $h_t$ and $X_t$ are the missing dimension and the increment of (39)–(40). Together with Azuma's inequality this yields Theorem 4.12.
--
--   Differences from the source:
--   - encoding: E[· | ℱ_{t−1}] → the average over the uniform new sample a_t for a fixed history (a_1, …, a_{t−1}) of any length; reason: conditioning on the history of independent uniform samples
--   - encoding: γ : [0, H] → [0, ∞) and the improper integral ∫_0^H du/γ(u) → γ : ℝ → ℝ, monotone and nonnegative on [0, H]; the integral is the lower Lebesgue integral of (ofReal γ(u))⁻¹ over [0, H] in [0, ∞], with 1/0 = ∞; reason: values off [0, H] are never used; the [0, ∞] integral of a nonnegative function is the improper integral, and 1/0 = ∞ keeps γ = 0 from making it small
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, Proposition 4.13, p.23 (proof p.29)

import Mathlib
import Definitions.Def_F3SubsetSum_TruncatedRing
import Definitions.Def_F3SubsetSum_SampleImage

namespace F3SubsetSum

/-- **Proposition 4.13** (Kothari, Metger, O'Donnell, Shutty, Wu, arXiv:2609.40321v1,
Proposition 4.13, p.23; proof p.29): "Assume 3 ≤ D ≤ n and let H = dim(R_D). There is a
nondecreasing function γ: [0, H] → [0, ∞) such that E[min{X_t/γ(h_{t−1}), 1} | ℱ_{t−1}] ≥ 1/3
holds for every h_{t−1} > 0, and ∫_0^H du/γ(u) ≤ 100n²/D."

Over `F_q`, `q ≥ 3` prime: `h_{t−1}` and `X_t` are `missingDim` and `increment` (eqs. (39)–(40),
p.24) for the history `a_1, …, a_{t−1}` and a uniform new sample `a_t ∈ F_qⁿ`. Conditioning on
`ℱ_{t−1}` means fixing the history: for every history (of any length) with `h_{t−1} > 0`, the
average over `a_t` of `min{X_t/γ(h_{t−1}), 1}` is at least `1/3`.

**Formalization Note** `γ` is a real function whose restriction to `[0, H]` is nondecreasing and
nonnegative. The improper integral is a Lebesgue integral of `[0, ∞]`-valued functions with
`1/0 = ∞` (`ENNReal` inverse), so a `γ` vanishing on a set of positive measure makes it
infinite, as in the paper's reading. -/
theorem proposition_4_13 (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) (n D : ℕ) (hD3 : 3 ≤ D)
    (hDn : D ≤ n) :
    ∃ γ : ℝ → ℝ,
      MonotoneOn γ (Set.Icc 0 (Module.finrank (ZMod q) (Rd (ZMod q) n q D) : ℝ)) ∧
      (∀ u ∈ Set.Icc 0 (Module.finrank (ZMod q) (Rd (ZMod q) n q D) : ℝ), 0 ≤ γ u) ∧
      (∀ (t : ℕ) (a : Fin t → Fin n → ZMod q), 0 < missingDim q a D →
        (1 : ℝ) / 3 ≤
          (∑ a' : Fin n → ZMod q,
              min ((increment q a a' D : ℝ) / γ (missingDim q a D)) 1) / (q : ℝ) ^ n) ∧
      ∫⁻ u in Set.Icc 0 (Module.finrank (ZMod q) (Rd (ZMod q) n q D) : ℝ),
          (ENNReal.ofReal (γ u))⁻¹ ≤ ENNReal.ofReal (100 * (n : ℝ) ^ 2 / D) := by sorry

end F3SubsetSum
