-- Prove2me | Theorems.Thm_DERAggregation_MarketPower_eq_60_64
-- name    : DERAggregation.MarketPower.eq_60_64
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:25:03.310664+00:00
-- url     : https://prove2.me/theorems/62604fda-3200-47af-898c-69ad3fd1d6fb
-- title:
--   (60), p. 29, with (63)–(64) of Proposition 6, p. 30 — the unique strategic outcome with participation and its price λ^S
-- statement:
--   Consider the single-node market of §5 with prosumer participation and strategic generators, under Assumption 5. A strategic outcome is a symmetric pure equilibrium of the quantity game (56): every generator supplies $q\ge0$, the market clears at total $Nq$ with price $\lambda$ and net purchases $z$, and no single generator gains by deviating to any $q'\ge0$ while the others keep $q$. Then $(q,\lambda,z)$ is a strategic outcome if and only if
--   $$q=y^S_j=\frac{-C+\sum_i\frac{\alpha-b_i}{2a_i}}{N+1}, \tag{60}$$
--   $$\lambda=\lambda^S=\frac{N\alpha}{N+1}+\frac{C+\sum_i\frac{b_i}{2a_i}}{(N+1)\sum_i\frac{1}{2a_i}}, \tag{64}$$
--   and $z_i=z^S_i=-C_i+(\lambda^S-b_i)/(2a_i)$ for every $i$ (63). In particular the strategic outcome with participation exists and is unique.
--
--   The supply $y^S=Ny^S_j$ is the fraction $N/(N+1)$ of the efficient supply, which drives every welfare comparison with participation.
--
--   **Formalization Note** The paper reaches (60) through the first-order condition of (59) and implements the quantity by the linear bid (62) (Lemma 5, Proposition 6); the bid layer is not modelled, and the outcome is the quantity equilibrium itself. Assumption 5 includes the readings H1, H2 of its informal clauses.
-- source:
--   Gao, Alshehri, Birge, Aggregating Distributed Energy Resources: Efficiency and Market Power, working paper, SSRN abstract 3931052 (PDF of September 26, 2021), §5.1.2, p. 29, (56), (59), (60); p. 30, Proposition 6, (63)–(64)

import Mathlib
import Definitions.Def_DERAggregation_MarketPower_Setting

namespace DERAggregation.MarketPower

open Finset

/-- (60), §5.1.2, p. 29, with (63)–(64) of Proposition 6, p. 30. Under Assumption 5, the strategic
outcomes with participation (symmetric pure equilibria of the quantity game (56)) are exactly
`y^S_j = (−C + Σ_i (α − b_i)/(2a_i))/(N + 1)` (60), at the price
`λ^S = Nα/(N + 1) + (C + Σ_i b_i/(2a_i)) / ((N + 1) Σ_i 1/(2a_i))` (64), with net purchases
`z^S_i = −C_i + (λ^S − b_i)/(2a_i)` (63). In particular such an outcome exists and is unique. -/
theorem eq_60_64 {ι : Type*} [Fintype ι] (a b C : ι → ℝ) (α : ℝ) (N : ℕ)
    (h5 : Assumption5 a b C α N) (q lam : ℝ) (z : ι → ℝ) :
    IsStratP a b C α N q lam z ↔
      (q = (-(∑ i, C i) + (∑ i, (α - b i) / (2 * a i))) / ((N : ℝ) + 1) ∧
        lam = (N : ℝ) * α / ((N : ℝ) + 1) +
          ((∑ i, C i) + (∑ i, b i / (2 * a i))) / (((N : ℝ) + 1) * (∑ i, 1 / (2 * a i))) ∧
        ∀ i, z i = -C i + (lam - b i) / (2 * a i)) := by sorry

end DERAggregation.MarketPower
