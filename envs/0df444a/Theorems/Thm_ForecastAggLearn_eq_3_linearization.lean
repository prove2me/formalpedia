-- Prove2me | Theorems.Thm_ForecastAggLearn_eq_3_linearization
-- name    : ForecastAggLearn.eq_3_linearization
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:26:12.557808+00:00
-- url     : https://prove2.me/theorems/7b9ef441-6767-4f7a-8493-dedbc86cef28
-- title:
--   Eq. (3) — in log-likelihood space $\tilde r^*=\tilde y\cdot\mathbf 1_m+\tilde\mu$ and $\tilde F=A\tilde y+\tilde\mu\mathbf 1_n$
-- statement:
--   Let $0<\mu<1$, let the conditional laws be probability measures, let $A$ be the evidence matrix of the sets $A_i$, and let $s$ be a signal profile. Write $\tilde\mu=\ln\frac{\mu}{1-\mu}$, $\tilde x_j=\ln\frac{x_j(s_j)}{1-x_j(s_j)}$ and $\tilde y=(\tilde x_j-\tilde\mu)_{j\in[m]}\in\mathbb R^m$. Then, where the $x_j(s_j)$ involved differ from $1$,
--
--   $$
--   \frac{r^*(s)}{1-r^*(s)}=\frac{(1-\mu)^{m-1}\prod_{j=1}^m x_j(s_j)}{\mu^{m-1}\prod_{j=1}^m(1-x_j(s_j))},\qquad
--   \frac{F_i(s)}{1-F_i(s)}=\frac{(1-\mu)^{|A_i|-1}\prod_{j\in A_i}x_j(s_j)}{\mu^{|A_i|-1}\prod_{j\in A_i}(1-x_j(s_j))},
--   $$
--
--   and, where the $x_j(s_j)$ involved lie in $(0,1)$, the log-likelihoods are linear in $\tilde y$:
--
--   $$
--   \tilde r^*(s)=\ln\frac{r^*(s)}{1-r^*(s)}=\tilde y\cdot\mathbf 1_m+\tilde\mu,\qquad
--   \tilde F(s)=\Bigl(\ln\frac{F_i(s)}{1-F_i(s)}\Bigr)_{i\in[n]}=A\tilde y+\tilde\mu\mathbf 1_n .
--   $$
--
--   This turns forecast aggregation into a linear problem: the aggregator sees $A\tilde y+\tilde\mu\mathbf 1_n$ and must report $\tilde y\cdot\mathbf 1_m+\tilde\mu$.
--
--   **Formalization Note** $r^*$, $F_i$ and $x_j$ are the density posteriors `post`; exponents are integers.
--
--   Differences from the source:
--   - encoding: (3) and the linear expressions without a domain → 0 < μ < 1; each odds identity where the x_j it involves differ from 1, each logarithmic identity where they lie in (0, 1); r*, F_i, x_j are post μ P univ, post μ P (A_i), post μ P {j}; reason: the quotients and logarithms are undefined outside these domains (for μ ∈ {0, 1} the odds identities are 0/0 or tautological); it excludes only undefined cases
-- source:
--   Babichenko, Garber, Learning of Optimal Forecast Aggregation in Partial Evidence Environments, arXiv:1802.07107v1, §4.1, eq. (3) and display, p.14

import Mathlib
import Definitions.Def_ForecastAggLearn_evidenceMatrix
import Definitions.Def_ForecastAggLearn_post

namespace ForecastAggLearn

open MeasureTheory

/-- **Eq. (3) and the linear model in log-likelihood space.**
Babichenko, Garber, arXiv:1802.07107v1, §4.1, eq. (3) and the display after it, p.14:

`r*/(1 − r*) = (1 − µ)^{m−1} Π_j x_j / (µ^{m−1} Π_j (1 − x_j))`,
`F_i/(1 − F_i) = (1 − µ)^{|A_i|−1} Π_{j∈A_i} x_j / (µ^{|A_i|−1} Π_{j∈A_i} (1 − x_j))`, and, with
`µ̃ = ln(µ/(1 − µ))`, `x̃_j = ln(x_j/(1 − x_j))`, `ỹ = (x̃_j − µ̃)_j`,
`r̃* = ỹ · 1_m + µ̃` and `F̃ = Aỹ + µ̃ 1_n`.

**Formalization Note.** `x_j = post μ P {j} s`, `r* = post μ P univ s`, `F_i = post μ P (A_i) s`,
and `A = evidenceMatrix Aset`. Each clause is stated where it is defined, for `0 < μ < 1`: the
odds identities (3) where the `x_j` they involve differ from `1` (the value `x_j = 0` is allowed),
the logarithmic identities where those `x_j` lie in `(0, 1)`. Exponents `m − 1`, `|A_i| − 1` are
integers (`zpow`). -/
theorem eq_3_linearization {n m : ℕ} (Aset : Fin n → Finset (Fin m))
    {S : Fin m → Type*} [∀ j, MeasurableSpace (S j)]
    (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (P : (j : Fin m) → Bool → Measure (S j))
    [∀ j b, IsProbabilityMeasure (P j b)] (s : (j : Fin m) → S j) :
    let x : Fin m → ℝ := fun j => post μ P {j} s
    let μt : ℝ := Real.log (μ / (1 - μ))
    let yt : Fin m → ℝ := fun j => Real.log (x j / (1 - x j)) - μt
    let rstar : ℝ := post μ P Finset.univ s
    let F : Fin n → ℝ := fun i => post μ P (Aset i) s
    ((∀ j, x j ≠ 1) → rstar / (1 - rstar) =
        ((1 - μ) ^ ((m : ℤ) - 1) * (∏ j, x j)) / (μ ^ ((m : ℤ) - 1) * (∏ j, (1 - x j)))) ∧
      (∀ i, (∀ j ∈ Aset i, x j ≠ 1) → F i / (1 - F i) =
        ((1 - μ) ^ (((Aset i).card : ℤ) - 1) * (∏ j ∈ Aset i, x j)) /
          (μ ^ (((Aset i).card : ℤ) - 1) * (∏ j ∈ Aset i, (1 - x j)))) ∧
      ((∀ j, x j ∈ Set.Ioo (0 : ℝ) 1) → Real.log (rstar / (1 - rstar)) = ∑ j, yt j + μt) ∧
      ∀ i, (∀ j ∈ Aset i, x j ∈ Set.Ioo (0 : ℝ) 1) →
        Real.log (F i / (1 - F i)) = (evidenceMatrix Aset).mulVec yt i + μt := by sorry

end ForecastAggLearn
