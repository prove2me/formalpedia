-- Prove2me | Theorems.Thm_BauerleRiederMDP_RegimeSwitching_theorem_4_4_4
-- name    : BauerleRiederMDP.RegimeSwitching.theorem_4_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:24:59.435883+00:00
-- url     : https://prove2.me/theorems/e5686514-3dd7-4270-a22a-3b08908146ca
-- title:
--   Theorem 4.4.4 — the optimal stock fraction is monotone in the icv order (corrected: $\alpha^*(k)\ge0$)
-- statement:
--   Consider one stock ($d=1$) in the regime-switching market of §4.4, with $R(j)>-1$ a.s., Assumption (FM) for every $j$, and the support of $R(j)$ independent of $j$, so that the admissible fractions $A(j)=\tilde A$ coincide. Let $0<\gamma<1$ and let $\alpha^*(j)$ be the optimal solution of
--
--   $$
--   v(j)=\sup_{\alpha\in\tilde A}\mathbb E\big(1+\alpha R(j)\big)^\gamma,\qquad j\in E_Y. \tag{4.21}
--   $$
--
--   If $Q_j\le_{icv}Q_k$ and $\alpha^*(k)\ge0$, then $\alpha^*(j)\le\alpha^*(k)$: the fraction of wealth invested in the stock in environment $k$ is at least the fraction invested in environment $j$.
--
--   **Formalization Note** "The optimal solution" is read as the unique maximizer: $\alpha^*(j)$ attains $v(j)$ and every maximizer equals it.
--
--   Differences from the source:
--   - correction: If Q_j ≤_icv Q_k, then α*(j) ≤ α*(k) → If Q_j ≤_icv Q_k and α*(k) ≥ 0, then α*(j) ≤ α*(k); reason: false for short positions: support {−0.5, −0.1, 0.3}, Q_j = (0.4, 0.2, 0.4), Q_k = (0.1, 0.8, 0.1) (Q_j a mean-preserving spread of Q_k, so Q_j ≤_icv Q_k), γ = 1/2: α*(j) ≈ −1.62 > α*(k) ≈ −3.04; the proof's y ↦ y/(1 + αy)^{1−γ} is convex for α < 0
--   - reading: α*(j) is the optimal solution of (4.21) → α*(j) attains v(j) and every maximizer in Ã equals α*(j) (hopt, huniq); reason: the definite article presupposes uniqueness; if R(j) = 0 a.s. (allowed by (FM), and then R(k) = 0 a.s. by the common support) every α ∈ Ã is optimal and the claim fails for an arbitrary choice
--   - encoding: the support of R(j) is independent of j; Q_j ≤_icv Q_k → equal supports (Measure.support) of the laws Q_j on Fin 1 → ℝ; IcvLE of their images under z ↦ z 0; reason: one stock is the coordinate 0 of a vector in ℝ^1
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 4.4.4, p.104 (PDF p.118); (4.21), p.104; proof p.105 (PDF p.119)

import Mathlib
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_NoArbitrageLaw
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_IcvLE
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_powerValue
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_RegimeMarket
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BauerleRiederMDP.RegimeSwitching

/-- **Theorem 4.4.4** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), p.104, PDF p.118), corrected. One stock (`d = 1`), the support of
`R(j)` independent of `j` (so `A(j) = Ã` for all `j`), Assumption (FM) and `R(j) > −1` a.s. for
every `j`, `0 < γ < 1`, and `α*(j)` the optimal solution of (4.21)
`v(j) = sup_{α ∈ Ã} 𝔼(1 + α R(j))^γ`. If `Q_j ≤_icv Q_k` and (correction) `α*(k) ≥ 0`, then
`α*(j) ≤ α*(k)`.

**Formalization Note.** "The optimal solution" is read as the unique maximizer: `α*(j)` attains
`v(j)` and every maximizer equals it (`huniq`); without uniqueness the claim fails (if `R(j) = 0`
a.s., which (FM) allows and which by the common support forces `R(k) = 0` a.s., every
`α ∈ Ã` is optimal). The hypothesis `α*(k) ≥ 0` corrects the printed statement, which is false
for short positions: on the common support `{−0.5, −0.1, 0.3}` take
`Q_j = (0.4, 0.2, 0.4)` and `Q_k = (0.1, 0.8, 0.1)` (a mean-preserving contraction, so
`Q_j ≤_icv Q_k`); with `γ = 1/2` the optimal fractions are `α*(j) ≈ −1.62 > α*(k) ≈ −3.04`. The
proof's function `y ↦ y/(1 + αy)^{1−γ}` is concave only for `α ≥ 0`. `Q_j` is a law on
`Fin 1 → ℝ`; the icv order compares its image on `ℝ`. -/
theorem theorem_4_4_4 {EY : Type*} [Fintype EY] (M : RegimeMarket EY 1)
    (hR : ∀ j, ∀ᵐ z ∂(M.Q j : Measure (Fin 1 → ℝ)), ∀ k, -1 < z k)
    (hNA : ∀ j, NoArbitrageLaw (M.Q j : Measure (Fin 1 → ℝ)))
    (hint : ∀ j, Integrable (fun z : Fin 1 → ℝ => ∑ k, |z k|) (M.Q j : Measure (Fin 1 → ℝ)))
    (hsupp : ∀ j k,
      (M.Q j : Measure (Fin 1 → ℝ)).support = (M.Q k : Measure (Fin 1 → ℝ)).support)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (αstar : EY → Fin 1 → ℝ)
    (hopt : ∀ j, αstar j ∈ admFrac (M.Q j : Measure (Fin 1 → ℝ)) ∧
        ∫⁻ z, ENNReal.ofReal ((1 + ∑ k, αstar j k * z k) ^ γ) ∂(M.Q j : Measure (Fin 1 → ℝ)) =
          powerValue (M.Q j : Measure (Fin 1 → ℝ)) γ)
    (huniq : ∀ j, ∀ α ∈ admFrac (M.Q j : Measure (Fin 1 → ℝ)),
        ∫⁻ z, ENNReal.ofReal ((1 + ∑ k, α k * z k) ^ γ) ∂(M.Q j : Measure (Fin 1 → ℝ)) =
          powerValue (M.Q j : Measure (Fin 1 → ℝ)) γ → α = αstar j)
    (j k : EY)
    (hicv : IcvLE ((M.Q j : Measure (Fin 1 → ℝ)).map (fun z => z 0))
      ((M.Q k : Measure (Fin 1 → ℝ)).map (fun z => z 0)))
    (hk : 0 ≤ αstar k 0) :
    αstar j 0 ≤ αstar k 0 := by sorry

end BauerleRiederMDP.RegimeSwitching
