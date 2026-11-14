-- Prove2me | Theorems.Thm_BilateralProfitLB_claim_3_4
-- name    : BilateralProfitLB.claim_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-13T19:19:10.566201+00:00
-- url     : https://prove2.me/theorems/20166472-d44b-41ad-9a36-7bb5295ac0d4
-- title:
--   Claim 3.4 — $h^0$ has a plateau of maximizers on $[1/4,1/2]$ with value $1/192$, and $h^j(q^\star_j)-\max_{q\notin I_j}h^j(q)\ge\Delta$
-- statement:
--   Let $K\ge1$, $w=1/(4K)$ and $\Delta=w^2/(384\cdot12)$. Let $h^j(q)=\mathbb E^j[\mathrm{Profit}(q/2,q)]$ be the expected profit of the prices $(q/2,q)$ under $\mathcal D_j$, for buyer prices $q\in[0,1]$. Then:
--
--   1. $h^0(q)\le 1/192$ for every $q\in[0,1]$, and for $q\in[0,1]$, $h^0(q)=1/192$ if and only if $q\in[1/4,1/2]$: the function $h^0$ has a plateau of maximizers on $[1/4,1/2]$, with maximum value $1/192$;
--   2. for every $j\in\{1,\dots,K\}$, with $q^\star_j$ the midpoint of $I_j$,
--   $$h^j(q^\star_j)-h^j(q)\ge\Delta\qquad\text{for every }q\in[0,1]\setminus I_j,$$
--   that is, $h^j(q^\star_j)-\max_{q\notin I_j}h^j(q)\ge\Delta$.
--
--   Every perturbed instance thus has its optimum inside its own interval $I_j$, by a margin $\Delta$ of order $1/K^2$, while the baseline does not single out any interval.
--
--   Differences from the source:
--   - reading: "$h^0$ has a plateau of maximizers in $[1/4,1/2]$" → on $[0,1]$ the maximizers of $h^0$ are exactly $[1/4,1/2]$; reason: the proof shows the first branch increasing and the last decreasing; this is the stronger reading
--   - reading: $\Delta=w^2/384\cdot12$ → $\Delta=w^2/(384\cdot12)$; reason: (76) and p.52 write $w^2/(384\cdot12)$; the other parse $12w^2/384$ makes (ii) false at $K=1$ (gain $\approx2.4\cdot10^{-5}<1/512$)
--   - encoding: $\max_{q\notin I_j}h^j(q)$ → a bound for every $q\in[0,1]\setminus I_j$; reason: buyer prices range over $[0,1]$ and the maximum is attained, so the two agree
--   - reading: $I_j$, a piece of a partition of $[1/4,1/2]$ with unspecified endpoints → $I_j=(a_j,a_j+w)$ open; reason: the strongest choice: (ii) then covers every $q\in[0,1]$ outside the open interval, including both endpoints, where $h^j=h^0\le1/192$, so it implies (ii) for every choice of endpoints
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Claim 3.4, p.51 (PDF 53), with eq. (76); first stated p.15 (PDF 17)

import Mathlib
import Definitions.Def_BilateralProfitLB_Construction

namespace BilateralProfitLB

/-- **Claim 3.4**, Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256 e91e8127…), p.15
(PDF 17), restated with its proof p.51 (PDF 53): for any `j = 1, …, K`,
(i) the function `h^0` has a plateau of maximizers in `[1/4, 1/2]`, with maximum value `1/192`;
(ii) letting `q⋆_j` be the midpoint of `I_j`, `h^j(q⋆_j) − max_{q ∉ I_j} h^j(q) ≥ ∆`, where
`∆ = w²/(384·12)`.

**Formalization Note.** Buyer prices range over `[0, 1]`. (i) is: `h^0 ≤ 1/192` on `[0, 1]`, and
on `[0, 1]` the maximizers are exactly `[1/4, 1/2]` (the proof shows the first branch increasing
and the last decreasing). (ii) is stated for every `q ∈ [0, 1] ∖ I_j`, which is the same as the
bound on the maximum (it is attained). `h^0` does not depend on `K`. -/
theorem claim_3_4 (K : ℕ) (hK : 1 ≤ K) :
    ((∀ q ∈ Set.Icc (0 : ℝ) 1, h K 0 q ≤ 1 / 192) ∧
        ∀ q ∈ Set.Icc (0 : ℝ) 1, (h K 0 q = 1 / 192 ↔ q ∈ Set.Icc (1 / 4 : ℝ) (1 / 2))) ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ K →
        ∀ q ∈ Set.Icc (0 : ℝ) 1, q ∉ I K j → Delta K ≤ h K j (qstar K j) - h K j q := by sorry

end BilateralProfitLB
