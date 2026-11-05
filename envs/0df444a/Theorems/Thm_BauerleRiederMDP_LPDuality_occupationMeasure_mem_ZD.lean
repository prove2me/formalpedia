-- Prove2me | Theorems.Thm_BauerleRiederMDP_LPDuality_occupationMeasure_mem_ZD
-- name    : BauerleRiederMDP.LPDuality.occupationMeasure_mem_ZD
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:31:06.134113+00:00
-- url     : https://prove2.me/theorems/8c47ddc8-ec54-437c-81cd-59f3b909875a
-- title:
--   §7.5.2 (pp.215–216) — discounted occupation measures lie in $\mathcal M_b$ and are feasible for (D)
-- statement:
--   Let $(E,A,D,Q,r,\beta)$ be a contracting Markov Decision Model: $b:E\to\mathbb R_+$ is a measurable bounding function with constants $c_r,\alpha_b\ge0$, i.e. $|r(x,a)|\le c_rb(x)$ and $\int b(x')Q(dx'\mid x,a)\le\alpha_bb(x)$ for $(x,a)\in D$, and $\beta\alpha_b<1$. Assume $b\ge1$ and $\int b\,dp<\infty$, and let $I\!M$ be a closed linear subspace of $\mathbb B_b$ with $b\in I\!M$. For a Markov policy $\pi\in F^\infty$ let $\mu_\pi$ be its discounted occupation measure. Then $\mu_\pi$ is a measure on $D$ with
--   $$
--   \mu_\pi(D)\le\sum_{k=0}^\infty\beta^k\,\mathbb E^\pi_p[b(X_k)]=\int b(x)\,\mu_\pi(d(x,a))\le\frac{\int b\,dp}{1-\beta\alpha_b}<\infty,
--   $$
--   so $\mu_\pi\in\mathcal M_b$, and $\mu_\pi$ is feasible for the dual program (D):
--   $$
--   \int\Big(v(x)-\beta\int v(x')Q(dx'\mid x,a)\Big)\mu_\pi(d(x,a))=\int v\,dp\qquad\text{for all } v\in I\!M,
--   $$
--   i.e. $\mu_\pi\in\mathcal Z_D$.
--
--   This is the feasibility half of weak duality, and with $\pi=(f^*,f^*,\dots)$ for a maximizer $f^*$ of $J_\infty$ it produces the optimal solution of (D) in the strong duality theorem.
--
--   **Formalization Note** $\mathcal Z_D$ and $\mathcal M_b$ are the platform definitions `MDPFinance.LPDuality.ZD` and `Mb`. The bound is stated in $[0,\infty]$, with $\int b\,dp/(1-\beta\alpha_b)$ a quotient of extended nonnegative reals.
--
--   Differences from the source:
--   - generalization: p is the initial distribution of X_0 (a probability measure) with ∫ b dp < ∞ → p is any measure on E with ∫ b dp < ∞; reason: every quantity is linear in p, so the result holds for every such measure; probability measures are the special case (Example 7.5.10 itself uses p ≡ 1 on two states)
--   - encoding: Q a stochastic kernel from D to E and r a measurable function on D → Q a Markov kernel and r a measurable function on E × A (platform MarkovDecisionModel); reason: only the values on D enter any statement; every kernel and reward on D extends to E × A
--   - encoding: measures μ on D with ∫ b dμ < ∞ → measures μ on E × A with μ(D) = μ(E × A) and ∫ b dμ < ∞ (platform Mb); reason: since b ≥ 1 such μ is finite, so μ(D) = μ(E × A) says μ is carried by D
--   - encoding: μ_π(B) = 𝔼^π_p[Σ β^k 1_B(X_k, A_k)] via the path measure ℙ^π_p → Σ_k β^k times the image of the law of X_k (iterated Measure.bind) under x ↦ (x, f_k(x)); reason: the two constructions have the same marginals, so they define the same measure
--   - encoding: the chain μ_π(D) ≤ Σ_k β^k 𝔼^π_p[b(X_k)] = ∫ b dμ_π ≤ ∫ b dp/(1 − βα_b) in ℝ → the same chain in [0, ∞] with lower Lebesgue integrals, 𝔼^π_p[b(X_k)] written as ∫ b dp_k for the law p_k of X_k; reason: b ≥ 0, so the lower Lebesgue integral is the integral; 1 − βα_b > 0
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §7.5.2, pp.215–216 (PDF 226–227), the display μ_π(D) ≤ … ≤ ∫ b dp/(1 − βα_b) < ∞ and the claim that μ_π is admissible for (D), proved in part b) of the proof of Theorem 7.5.6, p.217 (PDF 228)

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model
import Definitions.Def_MDPFinance_LPDuality_Bounding
import Definitions.Def_MDPFinance_LPDuality_Value
import Definitions.Def_MDPFinance_LPDuality_LP
import Definitions.Def_BauerleRiederMDP_LPDuality_stateLaw
import Definitions.Def_BauerleRiederMDP_LPDuality_occupationMeasure

open MeasureTheory ProbabilityTheory MDPFinance.LPDuality

namespace BauerleRiederMDP.LPDuality

/-- **Discounted occupation measures are feasible for the dual program (D)** (Bäuerle & Rieder,
*Markov Decision Processes with Applications to Finance* (2011), §7.5.2, pp.215–217, PDF 226–228:
the display on pp.215–216 and part b) of the proof of Theorem 7.5.6, announced on p.216 as "Later
in Theorem 7.5.6 it will be shown that `μ_π` is indeed admissible for (D)").

Setting of §7.5.2: a contracting model with bounding function `b` (`|r| ≤ c_r b`,
`∫ b dQ(·|x,a) ≤ α_b b` on `D`, `βα_b < 1`), `b ≥ 1`, `∫ b dp < ∞`, and `IM` a closed linear
subspace of `IB_b` with `b ∈ IM`. For every Markov policy `π ∈ F^∞` the occupation measure `μ_π`
lives on `D`, satisfies
`μ_π(D) ≤ ∑_{k=0}^∞ β^k 𝔼^π_p[b(X_k)] = ∫ b dμ_π ≤ ∫ b dp / (1 - βα_b) < ∞` (so `μ_π ∈ M_b`),
where `𝔼^π_p[b(X_k)] = ∫ b dp_k` with `p_k` the law of `X_k` (`stateLaw`), and `μ_π ∈ Z_D`.

**Formalization Note** `p` is any measure on `E` with `∫ b dp < ∞` (the book's initial
distribution is the case of a probability measure). The feasible set `Z_D` and `M_b` are the
platform definitions `MDPFinance.LPDuality.ZD`/`Mb`, which represent measures on `D` as measures on
`E × A` with `μ(D) = μ(E × A)`. -/
theorem occupationMeasure_mem_ZD {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    (M : MarkovDecisionModel E A) (b : E → ℝ) (cr αb : ℝ) (hb : IsBoundingFunction M b cr αb)
    (hb1 : ∀ x, 1 ≤ b x) (hαb : M.β * αb < 1) (IMs : Set (E → ℝ))
    (hIM : IsClosedSubspaceOf b IMs) (hbIM : b ∈ IMs)
    (p : Measure E) (hpb : ∫⁻ x, ENNReal.ofReal (b x) ∂p < ⊤)
    (π : ℕ → E → A) (hπ : IsPolicyOf M π) :
    occupationMeasure M π p M.Dᶜ = 0 ∧
      occupationMeasure M π p M.D ≤
        ∑' k, ENNReal.ofReal (M.β ^ k) * ∫⁻ x, ENNReal.ofReal (b x) ∂(stateLaw M π p k) ∧
      ∑' k, ENNReal.ofReal (M.β ^ k) * ∫⁻ x, ENNReal.ofReal (b x) ∂(stateLaw M π p k) =
        ∫⁻ xa, ENNReal.ofReal (b xa.1) ∂(occupationMeasure M π p) ∧
      ∫⁻ xa, ENNReal.ofReal (b xa.1) ∂(occupationMeasure M π p) ≤
        (∫⁻ x, ENNReal.ofReal (b x) ∂p) / ENNReal.ofReal (1 - M.β * αb) ∧
      occupationMeasure M π p ∈ ZD M b IMs p := by sorry

end BauerleRiederMDP.LPDuality
