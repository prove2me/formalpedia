-- Prove2me | Theorems.Thm_AddictivePlatforms_Costly_lemma_D_3
-- name    : AddictivePlatforms.Costly.lemma_D_3
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-16T14:38:33.902784+00:00
-- url     : https://prove2.me/theorems/936092b8-a6d6-435e-9a03-5a01e7f8ab09
-- title:
--   Lemma D.3, p. 36 — the unique joint-profit maximizing outcome has every platform at min{d¹_J, d²_J}
-- statement:
--   Work under Assumptions 1–3 with $K \ge 2$ platforms, a cap $\overline{A} > 0$ ($\overline{A} = \infty$ allowed) and a cost scale $\kappa > 0$, and let $A(\cdot)$ be the function of Lemma D.1. Then:
--   1. the problem
--   $$\max_{d \ge 0}\ \Big[\min\{A(Kd), \overline{A}\} - K\kappa\gamma(d)\Big] \qquad \text{(A.11)}$$
--   has a unique solution $d^1_J$;
--   2. there is a unique $d^2_J \ge 0$ at which the consumer's best payoff from joining all $K$ platforms, each with addictiveness $d^2_J$, is zero;
--   3. there is a joint-profit maximizing outcome (Definition 1) in which every platform chooses $\min\{d^1_J, d^2_J\}$, and in every joint-profit maximizing outcome every platform chooses $\min\{d^1_J, d^2_J\}$.
--
--   This is the benchmark without competition against which Proposition 5 measures the equilibrium of Lemma D.2: either the platforms' marginal trade-off ($d^1_J$) or the consumer's participation ($d^2_J$) determines the joint-profit maximizing addictiveness.
--
--   **Formalization Note.** Uniqueness of $d^1_J$ is asserted in the first sentence of the proof. "Unique outcome" is read as uniqueness of the platform profile (the consumer's off-path choices need not be unique). In Definition 1 the consumer, at every profile, chooses the better of "join all platforms with an optimal feasible attention profile" and "join none", and the platforms break ties among profit-maximizing profiles in the consumer's favour. Standing pins as in the model file, plus $K \ge 2$ and $\overline{A} > 0$.
-- source:
--   Ichihashi & Kim, Addictive Platforms, Bank of Canada SWP 2022-16 (Apr. 1, 2022), p. 36, Lemma D.3, (A.11), and its proof; p. 14, Definition 1

import Mathlib
import Definitions.Def_AddictivePlatforms_Costly_Model

open Set Filter Topology
open scoped ENNReal

namespace AddictivePlatforms.Costly

/-- Lemma D.3 (p. 36). Fix `K ≥ 2` platforms, a cap `Ā > 0` (`Ā = ∞` allowed), a cost scale
`κ > 0` and the function `A(·)` of Lemma D.1 (`AD`). Then (A.11) has a unique solution `d¹_J`,
there is a unique level `d²_J` at which the consumer's best payoff from joining all platforms is
zero, the profile in which every platform chooses `min{d¹_J, d²_J}` is a joint-profit maximizing
outcome (Definition 1), and in every joint-profit maximizing outcome every platform chooses
`min{d¹_J, d²_J}`. -/
theorem lemma_D_3 (v C γ g : ℝ → ℝ) (K : ℕ) (hK : 2 ≤ K) (hS : Standing v C γ g K)
    (Abar : ℝ≥0∞) (hAbar : 0 < Abar) (κ : ℝ) (hκ : 0 < κ) (AD : ℝ → ℝ) (hAD : IsAD C g K AD) :
    ∃ d1J d2J : ℝ,
      IsD1J AD γ κ Abar K d1J ∧ (∀ x : ℝ, IsD1J AD γ κ Abar K x → x = d1J) ∧
      IsD2J (uOf v) C Abar K d2J ∧ (∀ x : ℝ, IsD2J (uOf v) C Abar K x → x = d2J) ∧
      (∃ σ : AddictivePlatforms.Compete.ConsumerStrategy K,
        IsJPM (uOf v) C γ κ Abar (fun _ : Fin K => min d1J d2J) σ) ∧
      ∀ (d : Fin K → ℝ) (σ : AddictivePlatforms.Compete.ConsumerStrategy K), IsJPM (uOf v) C γ κ Abar d σ →
        ∀ k, d k = min d1J d2J := by sorry

end AddictivePlatforms.Costly
