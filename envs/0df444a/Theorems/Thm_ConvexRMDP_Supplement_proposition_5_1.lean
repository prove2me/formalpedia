-- Prove2me | Theorems.Thm_ConvexRMDP_Supplement_proposition_5_1
-- name    : ConvexRMDP.Supplement.proposition_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:58:29.89068+00:00
-- url     : https://prove2.me/theorems/e588ac47-1059-5f5f-916b-96ee9fb175d3
-- title:
--   Proposition 5.1 (corrected: Slater point feasible, in relint dom) — the worst case over $\mathcal U_{sa}$ equals the exponential-cone program (5.3)
-- statement:
--   Let $(\mathcal S, \mathcal A, r, \gamma, \mathcal U)$ be an sa-rectangular robust MDP satisfying Assumption 5.1 (with the corrected Slater condition) for constraint functions $g_{sa,1}, \dots, g_{sa,m}$. Let $(s,a) \in \mathcal S \times \mathcal A$ and $x \in [1,+\infty)^{\mathcal S}$. Then
--
--   $$
--   \min_{p \in \Delta(\mathcal S),\, g_{sa}(p) \le 0} \;\prod_{s' \in \mathcal S} x_{s'}^{\gamma p_{s'}} \;=\; \max\; \min_{s' \in \mathcal S}\{z_{s'} + y_{s'}\} + \Big(\frac{1-\gamma}{\gamma}\Big) u + \Big(\frac{1+\log\gamma}{\gamma}\Big)\alpha - \sum_{i=1}^m \xi_i\, g^*_{sa,i}\Big(\frac{y^i}{\xi_i}\Big)
--   $$
--
--   where the maximum is over $\xi \in \mathbb R^m_+$, $y, z \in \mathbb R^{\mathcal S}$, $u \in \mathbb R$, $\alpha \in \mathbb R_+$, $y^i \in \mathbb R^{\mathcal S}$ subject to $(x_{s'}, \alpha, z_{s'}) \in \mathcal K_{\exp}$ for all $s'$, $(1, \alpha, u) \in \mathcal K_{\exp}$ and $\sum_{i=1}^m y^i = y$ (the program (5.3)), and the maximum is attained.
--
--   This turns each inner minimization in the constraints of (4.7) into a conic maximization, which is how the conic program (5.10) of Theorem 5.1 is obtained.
--
--   **Formalization Note** The left side is an infimum over $\mathcal U_{sa}$ (a nonempty compact set under the assumption, so it is the minimum). The objective of (5.3) takes values in the extended reals because the perspective terms $\xi_i g^*_{sa,i}(y^i/\xi_i)$ (with the paper's convention at $\xi_i = 0$) may be $+\infty$; "max = value" is stated as: the value is attained at a feasible point and bounds every feasible objective value. In Lean the variables are a tuple $q = (\xi, y, z, u, \alpha, (y^i)_i)$.
--
--   Differences from the source:
--   - correction: Slater's condition of Assumption 5.1 ("$p \in \operatorname{relint}\Delta(\mathcal S)$ with $g_{sa,i}(p) < 0$ for non-affine $i$") → `Assumption51`, which also requires $p \in \operatorname{relint}\operatorname{dom}(g_{sa,i})$ for all $i$ and $g_{sa,i}(p) \le 0$ for affine $i$; reason: as printed the maximum need not be attained. For $\mathcal S=\{1,2,3\}$, $u=p_1-p_2$, $v=p_3-1/3$, $g_1=u^2-v$, $g_2=v$, the feasible set is the uniform point and $(1/4,1/4,1/2)$ satisfies the printed condition. With $x_1>1$, $x_2=x_3=1$, KKT stationarity at the uniform point is impossible in the $u$ direction, so no dual maximizer exists. The corrected condition is Boyd–Vandenberghe §5.2.3, cited in the proof.
--   - encoding: $\min$ over $\mathcal U_{sa}$ and $\max$ over (5.3) → `sInf` and `IsGreatest` of an `EReal`-valued objective; reason: Lean convention; the minimum exists and the attainment is stated.
-- source:
--   Grand-Clément & Petrik, arXiv:2209.10187v2, Proposition 5.1, display (5.3), p.16; proof pp.16–18 and App. D

import Mathlib
import Definitions.Def_ConvexRMDP_Supplement_Assumption51
import Definitions.Def_ConvexRMDP_Supplement_persp
import Definitions.Def_ConvexRMDP_Supplement_Kexp
import Definitions.Def_ConvexRMDP_Supplement_geoMean

namespace ConvexRMDP

namespace Supplement

/-- **Proposition 5.1 (corrected: Slater point feasible, in relint dom)** (Grand-Clément & Petrik,
arXiv:2209.10187v2, p.16; proof pp.16–18). Let `(s,a) ∈ S × A` and `x ∈ [1,+∞)^S`. Under Assumption
5.1,
`min_{p ∈ Δ(S), g_{sa}(p) ≤ 0} ∏_{s'} x_{s'}^{γ p_{s'}}
   = max min_{s'}{z_{s'} + y_{s'}} + ((1−γ)/γ) u + ((1+log γ)/γ) α − ∑_i ξ_i g*_{sa,i}(yⁱ/ξ_i)`
subject to `(x_{s'}, α, z_{s'}) ∈ 𝒦_exp` for all `s'`, `(1, α, u) ∈ 𝒦_exp`, `∑_i yⁱ = y`,
`ξ ∈ ℝ^m_+`, `y, z ∈ ℝ^S`, `u ∈ ℝ`, `α ∈ ℝ₊`, `yⁱ ∈ ℝ^S` — (5.3), the maximum being attained.

**Formalization Note.** Assumption 5.1 is `Assumption51` with the corrected Slater condition (see
that definition). The left side is `sInf` over `𝒰_{sa} = {p ∈ Δ(S) | g_{sa}(p) ≤ 0}` (nonempty and
compact under the assumption, so the minimum). The objective of (5.3) is `EReal`-valued because the
perspective terms `ξ_i g*_{sa,i}(yⁱ/ξ_i)` (`persp (conj g) ξ_i yⁱ`, with the paper's convention at
`ξ_i = 0`) may be `+∞`; "max … = value" is `IsGreatest`: the value is attained at a feasible point and
bounds every feasible objective value. The variables are `q = (ξ, y, z, u, α, yⁱ)`. `min_{s'}` is the
infimum over the finite nonempty `S`. -/
theorem proposition_5_1 {S A : Type*} [Fintype S] [Fintype A]
    (M : RMDP S A) (m : ℕ) (g : S → A → Fin m → (S → ℝ) → EReal)
    (hg : Assumption51 M m g) (s : S) (a : A) (x : S → ℝ) (hx : ∀ s', 1 ≤ x s') :
    IsGreatest
      ((fun q : (Fin m → ℝ) × (S → ℝ) × (S → ℝ) × ℝ × ℝ × (Fin m → S → ℝ) =>
          (((⨅ s', (q.2.2.1 s' + q.2.1 s')) + (1 - M.γ) / M.γ * q.2.2.2.1 +
              (1 + Real.log M.γ) / M.γ * q.2.2.2.2.1 : ℝ) : EReal) -
            ∑ i, persp (conj (g s a i)) (q.1 i) (q.2.2.2.2.2 i)) ''
        {q | (∀ s', (x s', q.2.2.2.2.1, q.2.2.1 s') ∈ Kexp) ∧
          ((1 : ℝ), q.2.2.2.2.1, q.2.2.2.1) ∈ Kexp ∧
          ∑ i, q.2.2.2.2.2 i = q.2.1 ∧ (∀ i, 0 ≤ q.1 i) ∧ 0 ≤ q.2.2.2.2.1})
      ((sInf (geoMean M.γ x '' M.U s a) : ℝ) : EReal) := by sorry

end Supplement

end ConvexRMDP
