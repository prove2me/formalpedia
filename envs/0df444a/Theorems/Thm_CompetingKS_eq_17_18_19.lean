-- Prove2me | Theorems.Thm_CompetingKS_eq_17_18_19
-- name    : CompetingKS.eq_17_18_19
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:17:23.850016+00:00
-- url     : https://prove2.me/theorems/fad9e570-42ae-4a6f-85f6-fbdaf8a4589c
-- title:
--   Eqs. (17)–(19) — normalized one-to-two profits and the supplier's disagreement point
-- statement:
--   Consider the one-to-two channel with $a=b=1$, $c=0$, and let $\eta\in[0,1]$, $w_i,w_j\in[0,1]$. The supplier's profit $\Pi_i(w_i,w_j)$ and retailer $i$'s profit $\pi_i(w_i,w_j)$ are
--   $$
--   \Pi_i=\begin{cases}w_j\frac{1-w_j}2&1-w_i\le\frac\eta2(1-w_j),\\[2pt] w_i\frac{2(1-w_i)-\eta(1-w_j)}{4-\eta^2}+w_j\frac{2(1-w_j)-\eta(1-w_i)}{4-\eta^2}&\frac\eta2(1-w_j)<1-w_i<\frac2\eta(1-w_j),\\[2pt] w_i\frac{1-w_i}2&1-w_i\ge\frac2\eta(1-w_j),\end{cases}
--   $$
--   $$
--   \pi_i=\begin{cases}0&1-w_i\le\frac\eta2(1-w_j),\\[2pt] \frac{(2(1-w_i)-\eta(1-w_j))^2}{(4-\eta^2)^2}&\frac\eta2(1-w_j)<1-w_i<\frac2\eta(1-w_j),\\[2pt] \frac{(1-w_i)^2}4&1-w_i\ge\frac2\eta(1-w_j),\end{cases}
--   $$
--   and the supplier's disagreement point is
--   $$
--   D_i(w_j)=w_j\frac{1-w_j}2.
--   $$
--
--   These are the explicit payoffs of the one-to-two bargaining unit.
--
--   Differences from the source:
--   - reading: the middle piece of (17) sums over i with the summand written for i → the sum over both products, with i, j swapped in the second term; reason: (17) reuses i as the summation index
--   - encoding: case conditions as ratios, with 2/η and 1/η → the same conditions with cleared denominators; reason: the ratios divide by η and by a − wⱼ; the cleared forms agree with the printed ones wherever those are defined and read 2/η as +∞ at η = 0, which changes no instance
-- source:
--   Feng, Li, Shanthikumar, Negotiations in Competing Supply Chains: The Kalai-Smorodinsky Bargaining Solution, accepted manuscript (Management Science, July 3, 2021), SSRN 3447674, eqs. (17), (18), (19), online appendix p.3

import Mathlib
import Definitions.Def_CompetingKS_unitOT

namespace CompetingKS

/-- Displays (17), (18), (19), Feng, Li, Shanthikumar, *Negotiations in Competing Supply Chains:
The Kalai-Smorodinsky Bargaining Solution*, accepted manuscript (Management Science, July 3, 2021),
SSRN 3447674, online appendix p.3: the profits and the supplier's disagreement point of the
normalized one-to-two channel (`a = b = 1`, `c = 0`), for `wᵢ, wⱼ ∈ [0, 1]`.

**Formalization Note** The sum in the middle piece of (17) reuses `i` as the summation index; it is
the sum over both products, with `i, j` swapped in the second term. Case conditions have cleared
denominators. -/
theorem eq_17_18_19 {η wi wj : ℝ} (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1)
    (hwi : wi ∈ Set.Icc (0 : ℝ) 1) (hwj : wj ∈ Set.Icc (0 : ℝ) 1) :
    (1 - wi ≤ η / 2 * (1 - wj) →
      supplierOT 1 1 0 η wi wj = wj * ((1 - wj) / 2) ∧ retailerOT 1 1 η wi wj = 0) ∧
    (η / 2 * (1 - wj) < 1 - wi → η * (1 - wi) < 2 * (1 - wj) →
      supplierOT 1 1 0 η wi wj =
        wi * ((2 * (1 - wi) - η * (1 - wj)) / (4 - η ^ 2)) +
          wj * ((2 * (1 - wj) - η * (1 - wi)) / (4 - η ^ 2)) ∧
      retailerOT 1 1 η wi wj = (2 * (1 - wi) - η * (1 - wj)) ^ 2 / (4 - η ^ 2) ^ 2) ∧
    (2 * (1 - wj) ≤ η * (1 - wi) →
      supplierOT 1 1 0 η wi wj = wi * ((1 - wi) / 2) ∧
      retailerOT 1 1 η wi wj = (1 - wi) ^ 2 / 4) ∧
    disagreeOT 1 1 0 η wj = wj * ((1 - wj) / 2) := by sorry

end CompetingKS
