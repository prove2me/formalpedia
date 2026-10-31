-- Prove2me | Theorems.Thm_CompetingKS_proposition_2
-- name    : CompetingKS.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:17:41.744077+00:00
-- url     : https://prove2.me/theorems/c4e6f5b2-4c20-4b90-b8e2-ea76fad55b6c
-- title:
--   Proposition 2 — the simultaneous KS equilibrium is unique, equals $c+(a-c)/5$ resp. $c+(1-\eta)(a-c)/(5-\eta)$, and is the NB equilibrium exactly at retailer power $3/5$
-- statement:
--   Let $a>c$ and $b>0$.
--
--   **One-to-two channel.** Let $\eta\in[0,1]$ and $\hat w=c+\frac{a-c}5$.
--
--   1. The simultaneous Kalai–Smorodinsky equilibrium exists, is unique, and equals $(\hat w,\hat w)$.
--   2. For $\theta\in[0,1]$, $(\hat w,\hat w)$ is a simultaneous Nash bargaining equilibrium with retailer bargaining power $\theta$ if and only if $\theta=\frac35$.
--   3. The simultaneous Nash bargaining equilibrium with $\theta=\frac35$ exists, is unique, and equals $(\hat w,\hat w)$.
--
--   **Two-to-one channel.** Let $\eta\in[0,1)$ and $\check w=c+\frac{(1-\eta)(a-c)}{5-\eta}$. The same three statements hold with $\check w$ in place of $\hat w$.
--
--   So in both channels the Kalai–Smorodinsky equilibrium coincides with the Nash bargaining equilibrium in which the retailer has power $0.6$, not the symmetric $0.5$, whatever the level of competition $\eta$. This is the paper's central finding under simultaneous negotiation without contingency.
--
--   **Formalization Note** A simultaneous equilibrium is a contract pair in $\hat{\mathcal C}$ (resp. $\check{\mathcal C}$) in which each contract is the solution of its bargaining unit given the other contract, over contracts in $[c,a]$. The Kalai–Smorodinsky solution is individual rationality, Pareto optimality and the proportional-surplus equation.
--
--   Differences from the source:
--   - encoding: η ∈ [0, 1] for the two-to-one channel → η ∈ [0, 1); reason: at η = 1, wᵢ = wⱼ < a Lemma 1(ii)(a) gives q*ᵢ = 0 and (ii)(c) gives q*ᵢ = (a − wᵢ)/(2b), and (ii)(b) divides by 1 − η² = 0, so q* and the profits are undefined there; this excludes only that undefined case
--   - reading: the negotiated wholesale prices are ŵ, w̌ → the simultaneous KS equilibrium exists, is unique and equals (ŵ, ŵ), resp. (w̌, w̌); reason: "the negotiated prices are" characterizes the equilibrium; the stronger reading; equilibrium is "the Nash equilibrium of the two bargaining problems", p.19
--   - reading: prices "equal to the corresponding NB solutions with the retailers' bargaining power being 0.6" → (ŵ, ŵ) is an NB(θ) equilibrium for θ ∈ [0, 1] if and only if θ = 3/5, and the NB(3/5) equilibrium is exactly that pair; same for (w̌, w̌); reason: the proof sets the NB equilibrium price equal to the KS price and solves for θ
--   - reading: the KS solution as equation (2) on a non-convex allocation set → individual rationality, Pareto optimality and (2) cross-multiplied; reason: the paper restricts (2) to Pareto allocations (online appendix p.5, pp.14–15); without Pareto every contract with allocation (D, d) satisfies (2) as 0 = 0
--   - encoding: contract space, in the channels → w ∈ [c, a]; reason: the contract space stated on p.15
--   - encoding: case conditions as ratios, with 2/η and 1/η → the same conditions with cleared denominators; reason: the ratios divide by η and by a − wⱼ; the cleared forms agree with the printed ones wherever those are defined and read 2/η as +∞ at η = 0, which changes no instance
--   - generalization: equilibria range over Ĉ, Č of (6), defined for wⱼ < a → the cleared forms also admit pairs with a coordinate equal to a; reason: uniqueness is then claimed over a larger set, which contains the source's; no such pair is an equilibrium
-- source:
--   Feng, Li, Shanthikumar, Negotiations in Competing Supply Chains: The Kalai-Smorodinsky Bargaining Solution, accepted manuscript (Management Science, July 3, 2021), SSRN 3447674, Proposition 2, pp.19–20

import Mathlib
import Definitions.Def_CompetingKS_unitOT

namespace CompetingKS

/-- Proposition 2 (Simultaneous Bargaining without Contingency), Feng, Li, Shanthikumar,
*Negotiations in Competing Supply Chains: The Kalai-Smorodinsky Bargaining Solution*, accepted
manuscript (Management Science, July 3, 2021), SSRN 3447674, pp.19–20.

For every `a > c`, `b > 0`. In the one-to-two channel, for every `η ∈ [0, 1]`, with
`ŵ = c + (a - c)/5`: the simultaneous KS equilibrium exists, is unique and equals `(ŵ, ŵ)`; `(ŵ, ŵ)`
is a simultaneous NB equilibrium with retailer power `θ ∈ [0, 1]` exactly when `θ = 3/5`; and the NB
equilibrium at `θ = 3/5` exists, is unique and equals `(ŵ, ŵ)`. In the two-to-one channel, for every
`η ∈ [0, 1)`, with `w̌ = c + (1 - η)(a - c)/(5 - η)`: the same three statements.

**Formalization Note** The two-to-one channel excludes `η = 1`, where the claimed `w̌ = c` lies on
the diagonal on which Lemma 1(ii) does not define `q*`. Equilibria are `IsKSEqOT`, `IsNBEqOT`,
`IsKSEqTO`, `IsNBEqTO`; the KS solution is `IsKSResponse`, individual rationality, Pareto optimality
and equation (2). -/
theorem proposition_2 {a b c : ℝ} (hac : c < a) (hb : 0 < b) :
    (∀ η : ℝ, 0 ≤ η → η ≤ 1 →
      (∀ w₁ w₂ : ℝ, IsKSEqOT a b c η w₁ w₂ ↔ w₁ = c + (a - c) / 5 ∧ w₂ = c + (a - c) / 5) ∧
      (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
        (IsNBEqOT a b c η θ (c + (a - c) / 5) (c + (a - c) / 5) ↔ θ = 3 / 5)) ∧
      (∀ w₁ w₂ : ℝ, IsNBEqOT a b c η (3 / 5) w₁ w₂ ↔
        w₁ = c + (a - c) / 5 ∧ w₂ = c + (a - c) / 5)) ∧
    (∀ η : ℝ, 0 ≤ η → η < 1 →
      (∀ w₁ w₂ : ℝ, IsKSEqTO a b c η w₁ w₂ ↔
        w₁ = c + (1 - η) * (a - c) / (5 - η) ∧ w₂ = c + (1 - η) * (a - c) / (5 - η)) ∧
      (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
        (IsNBEqTO a b c η θ (c + (1 - η) * (a - c) / (5 - η))
          (c + (1 - η) * (a - c) / (5 - η)) ↔ θ = 3 / 5)) ∧
      (∀ w₁ w₂ : ℝ, IsNBEqTO a b c η (3 / 5) w₁ w₂ ↔
        w₁ = c + (1 - η) * (a - c) / (5 - η) ∧ w₂ = c + (1 - η) * (a - c) / (5 - η))) := by sorry

end CompetingKS
