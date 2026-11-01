-- Prove2me | Theorems.Thm_DoublyOptBandit_theorem_3_8
-- name    : DoublyOptBandit.theorem_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:28:55.670213+00:00
-- url     : https://prove2.me/theorems/d87f5dd7-cdd1-4d98-b1ed-fb53c0f8a444
-- title:
--   Theorem 3.8 — Algorithm 2 converges to the Nash equilibrium of a strongly monotone game at last-iterate rate $\tilde O(nT^{-1/2})$
-- statement:
--   Consider $N\ge1$ players and parameters $L>0$, $\beta>0$, weights $\lambda_i>0$, and numbers $\ell_i,\nu_i,B_i,G_i$. Then there is a constant $C$, depending only on these parameters, with the following property.
--
--   Let $n_i\ge1$ be any dimensions and $n=\sum_in_i$. Let $G$ be a smooth and concave game whose action sets $X_i\subseteq\mathbb R^{n_i}$ have nonempty interior, such that
--
--   1. each $v_i$ is $\ell_i$-Lipschitz on $X$ and $\|v_i\|\le G_i$ on $X$;
--   2. $\operatorname{diam}X_i\le B_i$;
--   3. $|u_i(x)|\le L$ for all $x\in X$;
--   4. $G$ is $(\beta,\{\lambda_i\})$-strongly monotone;
--
--   and let $x^\star$ be its unique Nash equilibrium. Let $R_i$ be a $\nu_i$-self-concordant barrier for $X_i$ for each $i$, and let the directions $z_i^t$ be independent random vectors, each uniform on the unit sphere of $\mathbb R^{n_i}$. If every player runs Algorithm 2 with step size $\eta_t=\frac1{2nL\sqrt t}$, then for every $T\ge1$ the played profile $\hat x^T$ satisfies
--   $$
--   \mathbb E\Big[\sum_i\|\hat x_i^T-x_i^\star\|^2\Big]\le C\,\frac{n\,(1+\log T)}{\sqrt T},
--   $$
--   and the random variable inside the expectation is integrable. This is the paper's bound $\tilde O(nT^{-1/2})$, with the hidden constant made explicit.
--
--   The rate matches Shamir's lower bound $\Omega(nT^{-1/2})$ for bandit optimization of strongly convex smooth functions up to the logarithmic factor, and improves the $\tilde O(n^{2/3}T^{-1/3})$ rate of multi-agent FKM. Together with the $\tilde O(n\sqrt T)$ single-agent regret of Algorithm 1 (Theorem 2.10) it makes the algorithm "doubly optimal".
--
--   Differences from the source:
--   - reading: E[Σᵢ ‖x̂ᵢᵀ − x⋆ᵢ‖²] = Õ(nT^{−1/2}) → ∃ C depending only on (N, L, β, λ, ℓ, ν, B, G), chosen before the dimensions, the game, the barriers, the probability space and T, with E[…] ≤ C·n·(1 + log T)/√T for every T ≥ 1; reason: the paper does not say what the hidden constant depends on; the proof (pp.34–38) treats exactly these quantities as constants and extracts the factor n through Σᵢnᵢ²λᵢ ≤ n² maxᵢλᵢ; one logarithmic factor, written 1 + log T so that it is positive at T = 1 and absorbs the step Σ_{t<T} 1/t ≤ log T of p.35, which fails at T = 2
--   - reading: constants hidden in Õ for diameter and gradient size → diam Xᵢ ≤ Bᵢ and ‖vᵢ‖ ≤ Gᵢ on X as parameters of the constant; reason: the proof assumes diam Xᵢ ≤ Bᵢ (p.34) and bounds ‖∇ᵢuᵢ‖ on X "since X is compact" (p.37); every game has such Bᵢ, Gᵢ and Lipschitz constants ℓᵢ, so the per-instance bound follows
--   - reading: n in ηₜ = 1/(2nL√t) and in the rate → n = Σᵢ nᵢ; reason: Appendix E, p.33: "Since n = Σ_{i∈N} nᵢ in the multi-agent setting"
--   - encoding: dimensions nᵢ, N players, L, weights λᵢ, sets Xᵢ → nᵢ ≥ 1, N ≥ 1, L > 0, λᵢ > 0, int Xᵢ nonempty; reason: Sⁿⁱ is empty for nᵢ = 0; ηₜ = 1/(2nL√t) needs L > 0; Algorithm 2 takes λᵢ > 0 as input (footnote 6's λᵢ ≥ 0 is for Definition 3.4 only); Rᵢ : int(Xᵢ) → ℝ and the initialization need int Xᵢ ≠ ∅
--   - encoding: expectation E[·] over the draws → Bochner integral over a probability space, with integrability of the integrand as a conjunct of the conclusion; reason: rules out a vacuous bound from the value 0 of a non-integrable integral
--   - encoding: zᵢᵗ ∼ Sⁿⁱ drawn afresh by every player in every round → random variables, each uniform on the unit sphere (published IsUniformOnUnitSphere), mutually independent over all (t, i); the iterates are the pathwise iterates at the realized directions; reason: the same random process
--   - encoding: argmin over Xᵢ in (3.3) and in the initialization; (∇²Rᵢ + cI)^{−1/2} → argmin over int Xᵢ; the symmetric positive definite inverse square root; reason: Rᵢ is defined on int Xᵢ only; the inverse square root of a positive definite matrix is the symmetric one
-- source:
--   Ba, Lin, Zhang & Zhou, Doubly Optimal No-Regret Online Learning in Strongly Monotone Games with Bandit Feedback, arXiv:2112.02856v4, Theorem 3.8, p.15; proof, Appendix F, pp.34–38; Algorithm 2, p.15

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_SelfConcordantBarrier
import Definitions.Def_OnlineConvexOpt_BanditConvex_UniformOnUnitSphere_v2
import Definitions.Def_DoublyOptBandit_Algorithm2

open scoped InnerProductSpace
open MeasureTheory ProbabilityTheory

namespace DoublyOptBandit

/-- **Theorem 3.8** (last-iterate rate of Algorithm 2; Ba, Lin, Zhang & Zhou, arXiv:2112.02856v4,
Theorem 3.8, p.15): "Suppose that x⋆ ∈ X is a unique Nash equilibrium of a smooth and
(β, {λᵢ})-strongly monotone game. Each function uᵢ satisfies that |uᵢ(x)| ≤ L for all x ∈ X. If
T ≥ 1 is fixed and each player employs Algorithm 2 with the stepsize choice of ηₜ = 1/(2nL√t), we
have E[Σᵢ ‖x̂ᵢᵀ − x⋆ᵢ‖²] = Õ(nT^{−1/2})."

Reading of `Õ(nT^{−1/2})`: for given parameters — the number of players `N`, the reward bound
`L > 0`, the monotonicity modulus `β > 0`, the weights `λᵢ > 0`, the Lipschitz constants `ℓᵢ` of the
`vᵢ`, the barrier parameters `νᵢ`, the diameters `Bᵢ` of the `Xᵢ` and bounds `Gᵢ` on `‖vᵢ‖` over `X` —
there is one constant `C` such that for **every** choice of dimensions `nᵢ ≥ 1`, every such game,
barriers, unique Nash equilibrium, every probability space carrying independent uniform directions
and **every** `T ≥ 1`, the played profile `x̂ᵀ` of Algorithm 2 with `ηₜ = 1/(2nL√t)`, `n = Σᵢ nᵢ`,
satisfies `E[Σᵢ ‖x̂ᵢᵀ − x⋆ᵢ‖²] ≤ C · n · (1 + log T)/√T` (and the integrand is integrable).

**Formalization Note** Players are `Fin N`, `Xᵢ ⊆ EuclideanSpace ℝ (Fin (n i))`, the joint space is
`PiLp 2`. Rewards are total functions; every hypothesis is imposed on `X`. The barriers are the
published `EntropicBarrier.Universal.IsNuSelfConcordantBarrier`. The directions `zᵢᵗ` are random
variables, each uniform on the unit sphere (the published `IsUniformOnUnitSphere`), mutually
independent over all rounds and players; the iterates are the pathwise iterates of Algorithm 2
(`alg2Played`) evaluated at the realized directions. `Xᵢ` has nonempty interior (Algorithm 2
starts at the minimizer of `Rᵢ : int(Xᵢ) → ℝ`). The constant `C` is quantified before the
dimensions, the game, the barriers, the probability space and `T`, and after the parameters only. -/
theorem theorem_3_8 (N : ℕ) (hN : 1 ≤ N) (L β : ℝ) (hL : 0 < L) (hβ : 0 < β)
    (lam ℓ ν B G : Fin N → ℝ) (hlam : ∀ i, 0 < lam i) :
    ∃ C : ℝ, ∀ (n : Fin N → ℕ), (∀ i, 1 ≤ n i) →
      ∀ (game : SmoothConcaveGame n), (∀ i, (interior (game.X i)).Nonempty) →
      (∀ i, ∀ x ∈ jointSet game.X, ∀ x' ∈ jointSet game.X,
        ‖game.v x i - game.v x' i‖ ≤ ℓ i * ‖x - x'‖) →
      (∀ i, ∀ x ∈ jointSet game.X, ‖game.v x i‖ ≤ G i) →
      (∀ i, ∀ y ∈ game.X i, ∀ y' ∈ game.X i, ‖y - y'‖ ≤ B i) →
      (∀ i, ∀ x ∈ jointSet game.X, |game.u i x| ≤ L) →
      IsStronglyMonotone game β lam →
      ∀ xs : Joint n, IsNash game xs → (∀ y, IsNash game y → y = xs) →
      ∀ R : ∀ i, EuclideanSpace ℝ (Fin (n i)) → ℝ,
        (∀ i, EntropicBarrier.Universal.IsNuSelfConcordantBarrier (game.X i) (R i) (ν i)) →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (z : ℕ → ∀ i, Ω → EuclideanSpace ℝ (Fin (n i))),
        (∀ t i, OnlineConvexOpt.BanditConvex.IsUniformOnUnitSphere P (z t i)) →
        iIndepFun (fun p : ℕ × Fin N => z p.1 p.2) P →
      ∀ T : ℕ, 1 ≤ T →
        Integrable (fun ω => ∑ i,
          ‖alg2Played game.X R game.u lam β (stepSize n L) (fun t j => z t j ω) T i - xs i‖ ^ 2)
          P ∧
        ∫ ω, (∑ i,
          ‖alg2Played game.X R game.u lam β (stepSize n L) (fun t j => z t j ω) T i - xs i‖ ^ 2)
          ∂P ≤ C * (∑ i, (n i : ℝ)) * (1 + Real.log T) / Real.sqrt T := by sorry

end DoublyOptBandit
