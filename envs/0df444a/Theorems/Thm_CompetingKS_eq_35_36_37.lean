-- Prove2me | Theorems.Thm_CompetingKS_eq_35_36_37
-- name    : CompetingKS.eq_35_36_37
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:17:50.733677+00:00
-- url     : https://prove2.me/theorems/536144ce-22c3-43f9-9212-8a4180238a62
-- title:
--   Eqs. (35)–(37) — normalized two-to-one profits and the retailer's disagreement point
-- statement:
--   Consider the two-to-one channel with $a=b=1$, $c=0$, and let $\eta\in[0,1)$, $w_i,w_j\in[0,1]$. Supplier $i$'s profit $\Pi_i(w_i,w_j)$ and the retailer's profit $\pi_i(w_i,w_j)$ are
--   $$
--   \Pi_i=\begin{cases}0&1-w_i\le\eta(1-w_j),\\[2pt] w_i\frac{(1-w_i)-\eta(1-w_j)}{2(1-\eta^2)}&\eta(1-w_j)<1-w_i<\frac1\eta(1-w_j),\\[2pt] w_i\frac{1-w_i}2&1-w_i\ge\frac1\eta(1-w_j),\end{cases}
--   $$
--   $$
--   \pi_i=\begin{cases}\frac{(1-w_j)^2}4&1-w_i\le\eta(1-w_j),\\[2pt] \frac{(1-w_i)((1-w_i)-\eta(1-w_j))+(1-w_j)((1-w_j)-\eta(1-w_i))}{4(1-\eta^2)}&\eta(1-w_j)<1-w_i<\frac1\eta(1-w_j),\\[2pt] \frac{(1-w_i)^2}4&1-w_i\ge\frac1\eta(1-w_j),\end{cases}
--   $$
--   and the retailer's disagreement point is
--   $$
--   d_i(w_j)=\frac{(1-w_j)^2}4.
--   $$
--
--   These are the explicit payoffs of the two-to-one bargaining unit.
--
--   Differences from the source:
--   - reading: the middle piece of (36) sums over i with the summand written for i → the sum over both products, with i, j swapped in the second term; reason: (36) reuses i as the summation index
--   - encoding: case conditions as ratios, with 2/η and 1/η → the same conditions with cleared denominators; reason: the ratios divide by η and by a − wⱼ; the cleared forms agree with the printed ones wherever those are defined and read 2/η as +∞ at η = 0, which changes no instance
--   - encoding: η ∈ [0, 1] for the two-to-one channel → η ∈ [0, 1); reason: at η = 1, wᵢ = wⱼ < a Lemma 1(ii)(a) gives q*ᵢ = 0 and (ii)(c) gives q*ᵢ = (a − wᵢ)/(2b), and (ii)(b) divides by 1 − η² = 0, so q* and the profits are undefined there; this excludes only that undefined case
-- source:
--   Feng, Li, Shanthikumar, Negotiations in Competing Supply Chains: The Kalai-Smorodinsky Bargaining Solution, accepted manuscript (Management Science, July 3, 2021), SSRN 3447674, eqs. (35), (36), (37), online appendix p.9

import Mathlib
import Definitions.Def_CompetingKS_unitOT

namespace CompetingKS

/-- Displays (35), (36), (37), Feng, Li, Shanthikumar, *Negotiations in Competing Supply Chains:
The Kalai-Smorodinsky Bargaining Solution*, accepted manuscript (Management Science, July 3, 2021),
SSRN 3447674, online appendix p.9: the profits and the retailer's disagreement point of the
normalized two-to-one channel (`a = b = 1`, `c = 0`), for `η ∈ [0, 1)` and `wᵢ, wⱼ ∈ [0, 1]`.

**Formalization Note** The sum in the middle piece of (36) reuses `i` as the summation index; it is
the sum over both products, with `i, j` swapped in the second term. Case conditions have cleared
denominators. -/
theorem eq_35_36_37 {η wi wj : ℝ} (hη₀ : 0 ≤ η) (hη₁ : η < 1)
    (hwi : wi ∈ Set.Icc (0 : ℝ) 1) (hwj : wj ∈ Set.Icc (0 : ℝ) 1) :
    (1 - wi ≤ η * (1 - wj) →
      supplierTO 1 1 0 η wi wj = 0 ∧ retailerTO 1 1 η wi wj = (1 - wj) ^ 2 / 4) ∧
    (η * (1 - wj) < 1 - wi → η * (1 - wi) < 1 - wj →
      supplierTO 1 1 0 η wi wj = wi * (((1 - wi) - η * (1 - wj)) / (2 * (1 - η ^ 2))) ∧
      retailerTO 1 1 η wi wj =
        ((1 - wi) * ((1 - wi) - η * (1 - wj)) + (1 - wj) * ((1 - wj) - η * (1 - wi))) /
          (4 * (1 - η ^ 2))) ∧
    (1 - wj ≤ η * (1 - wi) →
      supplierTO 1 1 0 η wi wj = wi * ((1 - wi) / 2) ∧
      retailerTO 1 1 η wi wj = (1 - wi) ^ 2 / 4) ∧
    disagreeTO 1 1 η wj = (1 - wj) ^ 2 / 4 := by sorry

end CompetingKS
