-- Prove2me | Theorems.Thm_DeepMFC_FiniteHorizon_lemma_19
-- name    : DeepMFC.FiniteHorizon.lemma_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:47:03.298657+00:00
-- url     : https://prove2.me/theorems/bb405eba-5be9-4c54-a042-22447d0e3932
-- title:
--   Lemma 19, p. 4096 — (1/N)Σᵢ 𝔼|Xⁱ_t − Xⁱ_{t₀}|² ≤ C(1 + (1/N)Σᵢ 𝔼|Xⁱ_{t₀}|²)|t − t₀| for Lipschitz b, σ
-- statement:
--   Assume the standing initial-law condition $\mu_0\in\mathcal P_4(\mathbb R^d)$ and that $b$ and $\sigma$ are Lipschitz in all their variables: for some $L_b$ and all $t,t'\in[0,T]$, $x,x'\in\mathbb R^d$, $\mu,\mu'\in\mathcal P_2(\mathbb R^d)$, $\alpha,\alpha'\in\mathbb R^k$,
--   $$|b(t,x,\mu,\alpha)-b(t',x',\mu',\alpha')|\le L_b\big(|t-t'|+|x-x'|+W_2(\mu,\mu')+|\alpha-\alpha'|\big),$$
--   and every entry of $\sigma$ satisfies the same bound without the $\alpha$-term. Then for all $L,M\ge0$ there is a constant $C$ such that for every $N\ge1$, every feedback $\varphi$ that is $L$-Lipschitz in $(t,x)$ on $[0,T]\times\mathbb R^d$ with $|\varphi(0,0)|\le M$, every solution $(X^i)_{i\le N}$ of (3.2) controlled by $\varphi$, and all $0\le t_0\le t\le T$,
--   $$\frac1N\sum_{i=1}^N\mathbb E\big[|X^i_t-X^i_{t_0}|^2\big]\le C\Big(1+\frac1N\sum_{i=1}^N\mathbb E\big[|X^i_{t_0}|^2\big]\Big)|t-t_0|.\qquad(D.1)$$
--
--   This mean-square time regularity of the particle system, uniform in $N$, is one of the two estimates behind the $\sqrt{\Delta t}$ rate of the time discretization.
--
--   **Formalization Note.** The expectations are lower Lebesgue integrals in $[0,\infty]$. $C$ depends on the data (including $T$ and $L_b$), on the Lipschitz constant of $\varphi$ and on a bound for $|\varphi(0,0)|$; it is independent of $N$, $t_0$ and $t$. The initial-law condition comes from §2.2, p. 4067 and (B3), p. 4090. The Lipschitz hypothesis on $b,\sigma$ is the lemma's own, as printed; Remark 20 notes that it can be replaced by (A1).
-- source:
--   Carmona, Laurière, Convergence analysis of machine learning algorithms for the numerical solution of mean field control and games: II—the finite horizon case, Ann. Appl. Probab. 32(6) (2022), https://doi.org/10.1214/21-AAP1715, p. 4096, Appendix D, Lemma 19, (D.1)

import Mathlib
import Definitions.Def_DeepMFC_FiniteHorizon_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DeepMFC.FiniteHorizon

theorem lemma_19 {d k : ℕ} (M : Model d k) (hμ4 : IsP4 M.μ0) (Lb : ℝ)
    (hLip : ∀ t ∈ Set.Icc (0 : ℝ) M.T, ∀ t' ∈ Set.Icc (0 : ℝ) M.T, ∀ (x x' : E d)
      (μ μ' : Measure (E d)) (a a' : Fin k → ℝ), IsP2 μ → IsP2 μ' →
      ‖M.b t x μ a - M.b t' x' μ' a'‖ ≤ Lb * (|t - t'| + ‖x - x'‖ + (W2 μ μ').toReal + ‖a - a'‖) ∧
      ∀ i j : Fin d, |M.σ t x μ i j - M.σ t' x' μ' i j|
        ≤ Lb * (|t - t'| + ‖x - x'‖ + (W2 μ μ').toReal)) :
    ∀ L Mφ : ℝ, ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      ∀ φ : ℝ → E d → Fin k → ℝ, FeedbackLip M L φ → ‖φ 0 0‖ ≤ Mφ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : Fin N → ℝ≥0 → Ω → E d)
        (X0 : Fin N → Ω → E d), Setting3 M P W X0 →
      ∀ X : Fin N → ℝ≥0 → Ω → E d, Solves32 M P W X0 φ X →
      ∀ t₀ t : ℝ≥0, t₀ ≤ t → t ≤ M.T →
        (N : ℝ≥0∞)⁻¹ * ∑ i, ∫⁻ ω, ‖X i t ω - X i t₀ ω‖ₑ ^ 2 ∂P
          ≤ ENNReal.ofReal C * (1 + (N : ℝ≥0∞)⁻¹ * ∑ i, ∫⁻ ω, ‖X i t₀ ω‖ₑ ^ 2 ∂P)
            * ENNReal.ofReal ((t : ℝ) - t₀) := by sorry

end DeepMFC.FiniteHorizon
