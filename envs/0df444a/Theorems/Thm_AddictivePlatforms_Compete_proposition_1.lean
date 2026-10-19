-- Prove2me | Theorems.Thm_AddictivePlatforms_Compete_proposition_1
-- name    : AddictivePlatforms.Compete.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T12:58:21.190986+00:00
-- url     : https://prove2.me/theorems/a02564ae-daf9-4ad3-9b68-135137a33d37
-- title:
--   Proposition 1, p. 10 — monopoly addictiveness min{d^A(Ā), d^P(Ā)}, increasing in Ā; consumer payoff rises on [0, A(0)], falls on [A(0), Ā^M], is 0 beyond
-- statement:
--   Consider a single platform ($K = 1$) under Assumptions 1–2. Let $A(d)$ be the consumer's unconstrained attention choice, $d^A(\overline{A}) = \min\{d \in [0,\infty] : A(d) \ge \overline{A}\}$ the lowest addictiveness at which she exhausts her attention, and $d^P(\overline{A})$ the addictiveness at which her best capped payoff $\max_{A\in[0,\overline{A}]} u(A,d) - C(A)$ equals zero. Then:
--   1. $d^P(\overline{A})$ exists for every cap $\overline{A} \in \mathbb{R}_+ \cup \{\infty\}$;
--   2. for every cap $\overline{A} > 0$ a monopoly equilibrium (with the platform breaking ties in the consumer's favour) exists, and every monopoly equilibrium sets
--   $$d^M(\overline{A}) = \min\{d^A(\overline{A}),\, d^P(\overline{A})\};$$
--   3. $\overline{A} \mapsto \min\{d^A(\overline{A}), d^P(\overline{A})\}$ is (weakly) increasing;
--   4. there is $\overline{A}^M > A(0)$ such that the consumer's monopoly-equilibrium payoff, as a function of $\overline{A}$, is (weakly) increasing on $[0, A(0)]$, (weakly) decreasing on $[A(0), \overline{A}^M]$, and equal to zero on $[\overline{A}^M, \infty]$.
--
--   The result characterizes the monopoly benchmark against which Proposition 3 compares duopoly: when attention is scarce the monopolist does not need addictiveness at all, and when it is abundant it extracts the whole surplus.
--
--   **Formalization Note.** "Increasing" and "decreasing" are weak, the paper's convention (Appendix A proves exactly the weak inequalities). Item 2 is stated for $\overline{A} > 0$ (pin): at $\overline{A} = 0$ with $u(0,0) = 0$, as on the paper's own Figure 3 instance, every $d \ge 0$ is a monopoly equilibrium. The cap ranges over `ℝ≥0∞`, so $[\overline{A}^M, \infty]$ includes $\overline{A} = \infty$, and $\overline{A}^M$ is a real number. $A(d)$ is a parameter `Aopt` characterized by `IsUncChoice`; the standing hypotheses include the strict-concavity and $C(0)=0$ pins and the existence pin for one platform.
-- source:
--   Ichihashi & Kim, Addictive Platforms, Bank of Canada SWP 2022-16 (Apr. 1, 2022), p. 10, Proposition 1; proof Appendix A, pp. 26–28

import Mathlib
import Definitions.Def_AddictivePlatforms_Compete_Model

open Set Filter Topology
open scoped ENNReal

namespace AddictivePlatforms.Compete

/-- Proposition 1 (p. 10). Under the standing hypotheses, with `Aopt` the unconstrained choice
`A(d)`: `d^P(Ā)` exists for every cap; for every cap `Ā > 0` a monopoly equilibrium exists and every
monopoly equilibrium sets `min {d^A(Ā), d^P(Ā)}`; this addictiveness is (weakly) increasing in `Ā`;
and there is `Ā^M > A(0)` such that the consumer's monopoly-equilibrium payoff is increasing on
`[0, A(0)]`, decreasing on `[A(0), Ā^M]` and zero on `[Ā^M, ∞]`. -/
theorem proposition_1 (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (Aopt : ℝ → ℝ)
    (hS : Standing u C) (hE : UncOptExists u C 1) (hA : IsUncChoice u C Aopt) :
    (∀ Abar : ℝ≥0∞, ∃ dP : ℝ, IsDP u C Abar dP) ∧
    (∀ Abar : ℝ≥0∞, 0 < Abar → ∀ dP : ℝ, IsDP u C Abar dP →
      (∃ (d : Fin 1 → ℝ) (σ : ConsumerStrategy 1), IsMonopolyEq u C Abar d σ ∧
          ENNReal.ofReal (d 0) = min (dA Aopt Abar) (ENNReal.ofReal dP)) ∧
      ∀ (d : Fin 1 → ℝ) (σ : ConsumerStrategy 1), IsMonopolyEq u C Abar d σ →
          ENNReal.ofReal (d 0) = min (dA Aopt Abar) (ENNReal.ofReal dP)) ∧
    (∀ Abar₁ Abar₂ : ℝ≥0∞, Abar₁ ≤ Abar₂ → ∀ dP₁ dP₂ : ℝ,
      IsDP u C Abar₁ dP₁ → IsDP u C Abar₂ dP₂ →
        min (dA Aopt Abar₁) (ENNReal.ofReal dP₁) ≤ min (dA Aopt Abar₂) (ENNReal.ofReal dP₂)) ∧
    (∃ AM : ℝ, Aopt 0 < AM ∧
      (∀ Abar₁ Abar₂ : ℝ≥0∞, Abar₁ ≤ Abar₂ → Abar₂ ≤ ENNReal.ofReal (Aopt 0) →
        ∀ (d₁ : Fin 1 → ℝ) (σ₁ : ConsumerStrategy 1) (d₂ : Fin 1 → ℝ) (σ₂ : ConsumerStrategy 1),
          IsMonopolyEq u C Abar₁ d₁ σ₁ → IsMonopolyEq u C Abar₂ d₂ σ₂ →
            consumerSurplus u C d₁ σ₁ ≤ consumerSurplus u C d₂ σ₂) ∧
      (∀ Abar₁ Abar₂ : ℝ≥0∞, ENNReal.ofReal (Aopt 0) ≤ Abar₁ → Abar₁ ≤ Abar₂ →
        Abar₂ ≤ ENNReal.ofReal AM →
        ∀ (d₁ : Fin 1 → ℝ) (σ₁ : ConsumerStrategy 1) (d₂ : Fin 1 → ℝ) (σ₂ : ConsumerStrategy 1),
          IsMonopolyEq u C Abar₁ d₁ σ₁ → IsMonopolyEq u C Abar₂ d₂ σ₂ →
            consumerSurplus u C d₂ σ₂ ≤ consumerSurplus u C d₁ σ₁) ∧
      (∀ Abar : ℝ≥0∞, ENNReal.ofReal AM ≤ Abar →
        ∀ (d : Fin 1 → ℝ) (σ : ConsumerStrategy 1), IsMonopolyEq u C Abar d σ →
          consumerSurplus u C d σ = 0)) := by sorry

end AddictivePlatforms.Compete
