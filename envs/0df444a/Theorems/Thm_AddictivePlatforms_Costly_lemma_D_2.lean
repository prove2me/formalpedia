-- Prove2me | Theorems.Thm_AddictivePlatforms_Costly_lemma_D_2
-- name    : AddictivePlatforms.Costly.lemma_D_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T14:38:47.107968+00:00
-- url     : https://prove2.me/theorems/e63454d9-3b36-4458-af7e-c2c8a86eeefa
-- title:
--   Lemma D.2, p. 35 — the unique equilibrium has every platform at min{d¹(κ), d²}; d¹(κ) decreasing from ∞ to 0; equilibrium at d² iff κ ≤ κ^E
-- statement:
--   Work under Assumptions 1–3 with $K \ge 2$ platforms and a cap $\overline{A} > 0$ ($\overline{A} = \infty$ allowed). Let $A(\cdot)$ be the function of Lemma D.1, characterized by $A(D) \ge 0$ and $A(D) - D = K g(C'(A(D)))$ for $D \ge 0$, and let $d^2 > 0$ be the equilibrium addictiveness without costs: at $d^2$ the consumer is indifferent between joining $K$ and $K-1$ platforms that all choose $d^2$ (equation (3)). For $\kappa > 0$ put
--   $$\Pi(x,d) = \frac{1}{K}\Big[\min\{A(x + (K-1)d), \overline{A}\} - x - (K-1)d\Big] + x - \kappa\gamma(x). \qquad \text{(A.10)}$$
--   Then there is a function $\kappa \mapsto d^1(\kappa)$ such that:
--   1. for every $\kappa > 0$, $d^1(\kappa)$ is the unique $d^1 \ge 0$ with
--   $$d^1 \in \arg\max_{x \ge 0} \Pi(x, d^1); \qquad \text{(A.9)}$$
--   2. $d^1$ is decreasing on $(0,\infty)$, $\lim_{\kappa\to0} d^1(\kappa) = \infty$ and $\lim_{\kappa\to\infty} d^1(\kappa) = 0$;
--   3. for every $\kappa > 0$, $\min\{d^1(\kappa), d^2\} > 0$, there is a pure-strategy subgame perfect equilibrium in which every platform chooses $\min\{d^1(\kappa), d^2\}$, and in every such equilibrium every platform chooses $\min\{d^1(\kappa), d^2\}$;
--   4. there is $\kappa^E$ such that for every $\kappa > 0$ the equilibrium addictiveness equals $d^2$ if and only if $\kappa \le \kappa^E$.
--
--   The lemma splits the equilibrium into two regimes: for low costs the consumer's participation constraint binds and the outcome is the cost-free one, $d^2$; for high costs each platform's marginal trade-off between attention and the cost of addictiveness determines $d^1(\kappa)$.
--
--   **Formalization Note.** "Decreasing" is read weakly. The equilibrium is the equilibrium of the game with the consumer's true optimal choices; (A.10) is used only to define $d^1(\kappa)$, as on the page. $A(\cdot)$ and $d^2$ are passed as parameters together with their defining properties (their existence is Lemma D.1 and Step 1 of the proof of Proposition 2). "Unique equilibrium" is read as: every equilibrium has the same platform profile (the consumer's off-path choices need not be unique). Standing pins as in the model file, plus $K \ge 2$ and $\overline{A} > 0$ (at $\overline{A} = 0$ every platform's attention is zero and the equilibrium addictiveness is $0$).
-- source:
--   Ichihashi & Kim, Addictive Platforms, Bank of Canada SWP 2022-16 (Apr. 1, 2022), p. 35, Lemma D.2, (A.9), (A.10), and its proof (pp. 35–36)

import Mathlib
import Definitions.Def_AddictivePlatforms_Costly_Model

open Set Filter Topology
open scoped ENNReal

namespace AddictivePlatforms.Costly

/-- Lemma D.2 (p. 35). Fix `K ≥ 2` platforms, a cap `Ā > 0` (`Ā = ∞` allowed), the function
`A(·)` of Lemma D.1 (`AD`), and the no-cost equilibrium addictiveness `d² > 0` (`d2`), which
makes the consumer indifferent between joining `K` and `K − 1` platforms (equation (3)). Then
there is a function `κ ↦ d¹(κ)` such that, for every `κ > 0`, `d¹(κ)` is the unique solution of
(A.9); `d¹` is (weakly) decreasing on `(0, ∞)`, `d¹(κ) → ∞` as `κ → 0⁺` and `d¹(κ) → 0` as
`κ → ∞`; for every `κ > 0` the addictiveness `min{d¹(κ), d²}` is positive, the profile in which
every platform chooses it is supported by an equilibrium, and in every equilibrium every platform
chooses it; and there is `κ^E` such that, for every `κ > 0`, the equilibrium addictiveness equals
`d²` if and only if `κ ≤ κ^E`. -/
theorem lemma_D_2 (v C γ g : ℝ → ℝ) (K : ℕ) (hK : 2 ≤ K) (hS : Standing v C γ g K)
    (Abar : ℝ≥0∞) (hAbar : 0 < Abar) (AD : ℝ → ℝ) (hAD : IsAD C g K AD)
    (d2 : ℝ) (hd2 : 0 < d2 ∧ AddictivePlatforms.Compete.Eq3 (uOf v) C Abar K d2) :
    ∃ d1 : ℝ → ℝ,
      (∀ κ : ℝ, 0 < κ → IsD1 AD γ κ Abar K (d1 κ) ∧
        ∀ x : ℝ, IsD1 AD γ κ Abar K x → x = d1 κ) ∧
      AntitoneOn d1 (Ioi 0) ∧
      Tendsto d1 (𝓝[>] 0) atTop ∧
      Tendsto d1 atTop (𝓝 0) ∧
      (∀ κ : ℝ, 0 < κ →
        0 < min (d1 κ) d2 ∧
        (∃ σ : AddictivePlatforms.Compete.ConsumerStrategy K,
          IsSPE (uOf v) C γ κ Abar (fun _ : Fin K => min (d1 κ) d2) σ) ∧
        ∀ (d : Fin K → ℝ) (σ : AddictivePlatforms.Compete.ConsumerStrategy K), IsSPE (uOf v) C γ κ Abar d σ →
          ∀ k, d k = min (d1 κ) d2) ∧
      ∃ κE : ℝ, ∀ κ : ℝ, 0 < κ → (min (d1 κ) d2 = d2 ↔ κ ≤ κE) := by sorry

end AddictivePlatforms.Costly
