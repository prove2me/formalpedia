-- Prove2me | Theorems.Thm_AddictivePlatforms_Costly_proposition_5
-- name    : AddictivePlatforms.Costly.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T14:38:32.520979+00:00
-- url     : https://prove2.me/theorems/6f814739-2c78-4ce0-8541-1063edf05e8a
-- title:
--   Proposition 5, p. 17 — with cost κγ(d): unique symmetric positive equilibrium; joint-profit maximization gives lower d_k and higher consumer surplus iff κ ≥ κ*
-- statement:
--   Each of $K \ge 2$ platforms chooses an addictiveness $d_k \ge 0$ at cost $\kappa\gamma(d_k)$, and the consumer joins platforms and allocates attention under the cap $\overline{A}$, with $u(a,d) = v(a-d)$ and Assumptions 1–3. Then:
--   1. for every $\kappa > 0$ and every $\overline{A} > 0$ ($\overline{A} = \infty$ allowed) there is a $d > 0$ such that some pure-strategy subgame perfect equilibrium has every platform choose $d$, and every equilibrium has every platform choose $d$;
--   2. for every $\kappa > 0$ and $\overline{A} > 0$ a joint-profit maximizing outcome (Definition 1) exists;
--   3. for every $\overline{A} > 0$, including $\overline{A} = \infty$, there is $\kappa^* \in \mathbb{R}_+$ such that for every $\kappa > 0$
--   $$\Big[\ d^J_k \le d^E_k \ \text{ for all } k \quad\text{and}\quad U^E \le U^J\ \Big] \iff \kappa \ge \kappa^*,$$
--   where the left side is required for every joint-profit maximizing outcome $(d^J,\sigma^J)$ and every equilibrium $(d^E,\sigma^E)$, and $U^J$, $U^E$ are the consumer's payoffs at them.
--
--   By Lemmas D.2 and D.3 the equilibrium and the joint-profit maximizing outcome are unique, so the left side compares two well-defined outcomes. The proposition reverses the paper's cost-free comparison for abundant attention: when raising addictiveness is costly enough, competition makes platforms more addictive than joint-profit maximization and lowers consumer surplus, whatever the cap.
--
--   **Formalization Note.** "Lower" and "higher" are read weakly: the proof establishes $U^J(\kappa) \le U^E(\kappa)$ for $\kappa \le \kappa^*$ and $U^J(\kappa) \ge U^E(\kappa)$ for $\kappa \ge \kappa^*$, and at $\kappa = \kappa^*$ the two outcomes can coincide; the strict reading is not what is proved. Part 2 is the existence that the page's "the joint-profit maximizing outcome" presupposes (Lemma D.3); it keeps part 3 from holding vacuously. $\kappa$ ranges over $(0,\infty)$, as in Assumption 3; the proof's $\kappa = 0$ is the cost-free benchmark and is not part of the statement. $\kappa^*$ may depend on $\overline{A}$ and the primitives but not on $\kappa$. Standing pins as in the model file (strict concavity of $u(\cdot,d)$, $C(0) = 0$, existence of the uncapped optimum, the reading of $g = (v')^{-1}$, cost paid whether or not the consumer joins), plus $K \ge 2$ and $\overline{A} > 0$.
-- source:
--   Ichihashi & Kim, Addictive Platforms, Bank of Canada SWP 2022-16 (Apr. 1, 2022), p. 17, Proposition 5; proof Appendix D, pp. 33–37

import Mathlib
import Definitions.Def_AddictivePlatforms_Costly_Model

open Set Filter Topology
open scoped ENNReal

namespace AddictivePlatforms.Costly

/-- Proposition 5 (p. 17). Under the standing hypotheses of §5 with `K ≥ 2` platforms:
(i) for every cost scale `κ > 0` and every cap `Ā > 0` (`Ā = ∞` allowed) there is a positive
addictiveness `d` such that the profile in which every platform chooses `d` is supported by an
equilibrium, and in every equilibrium every platform chooses `d`;
(ii) for every `κ > 0` and `Ā > 0` a joint-profit maximizing outcome exists;
(iii) for every cap `Ā > 0` (`Ā = ∞` allowed) there is `κ* ≥ 0` such that for every `κ > 0`:
in every joint-profit maximizing outcome and every equilibrium, each `d_k` is (weakly) lower and
consumer surplus (weakly) higher under the joint-profit maximizing outcome, if and only if
`κ ≥ κ*`. -/
theorem proposition_5 (v C γ g : ℝ → ℝ) (K : ℕ) (hK : 2 ≤ K) (hS : Standing v C γ g K) :
    (∀ κ : ℝ, 0 < κ → ∀ Abar : ℝ≥0∞, 0 < Abar →
      ∃ x : ℝ, 0 < x ∧
        (∃ σ : AddictivePlatforms.Compete.ConsumerStrategy K, IsSPE (uOf v) C γ κ Abar (fun _ : Fin K => x) σ) ∧
        ∀ (d : Fin K → ℝ) (σ : AddictivePlatforms.Compete.ConsumerStrategy K), IsSPE (uOf v) C γ κ Abar d σ →
          ∀ k, d k = x) ∧
    (∀ κ : ℝ, 0 < κ → ∀ Abar : ℝ≥0∞, 0 < Abar →
      ∃ (d : Fin K → ℝ) (σ : AddictivePlatforms.Compete.ConsumerStrategy K), IsJPM (uOf v) C γ κ Abar d σ) ∧
    ∀ Abar : ℝ≥0∞, 0 < Abar → ∃ κstar : ℝ, 0 ≤ κstar ∧ ∀ κ : ℝ, 0 < κ →
      ((∀ (dJ : Fin K → ℝ) (σJ : AddictivePlatforms.Compete.ConsumerStrategy K), IsJPM (uOf v) C γ κ Abar dJ σJ →
          ∀ (dE : Fin K → ℝ) (σE : AddictivePlatforms.Compete.ConsumerStrategy K), IsSPE (uOf v) C γ κ Abar dE σE →
            (∀ k, dJ k ≤ dE k) ∧
              AddictivePlatforms.Compete.consumerSurplus (uOf v) C dE σE ≤ AddictivePlatforms.Compete.consumerSurplus (uOf v) C dJ σJ) ↔
        κstar ≤ κ) := by sorry

end AddictivePlatforms.Costly
