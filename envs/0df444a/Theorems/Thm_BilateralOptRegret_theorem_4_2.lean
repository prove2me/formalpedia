-- Prove2me | Theorems.Thm_BilateralOptRegret_theorem_4_2
-- name    : BilateralOptRegret.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:42:21.37618+00:00
-- url     : https://prove2.me/theorems/455600ef-3380-4270-84ed-399fd9de4364
-- title:
--   Theorem 4.2 — any refinement oracle gives regret $O(c_2\sqrt{A}\,T^{2/3})$, with (8)
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $T\ge2$, $c_1,c_2>0$, let $A$ be positive, and let Refine be a $(c_1,c_2,A)$-refinement oracle at $K=K(T)$. Then for every law $L$ on $[0,1]^2$, Algorithm 1 with the parameters (5) satisfies, when $\varepsilon_\star<1/8$ and with $\varepsilon_m=8^{-m}$,
--   $$R_T\le 16c_2A(K,\delta)\big(\varepsilon_m^{-2}+K\varepsilon_m^{-1}\big)+2T\varepsilon_m+2Tm\delta+\frac{2T}{K-1},$$
--   which is inequality (8), and in all cases
--   $$R_T\le C\,c_2\,\max\big(1,\sqrt{A(K,\delta)}\big)\,T^{2/3}.$$
--   This is the regret guarantee of the outer algorithm, with the refinement procedure treated as a black box.
--
--   **Formalization Note** The constant $C$ precedes all other quantifiers; in particular it does not depend on $c_1$, $c_2$, $A$, Refine, or $L$.
--
--   Differences from the source:
--   - reading: $R_T=O(c_2\sqrt{A(K,\delta)}\,T^{2/3})$ → inequality (8), together with $R_T\le C c_2\max(1,\sqrt{A(K,\delta)})T^{2/3}$; reason: the printed $O(\cdot)$ is ambiguous for $A<1$, where the term $2T/(K-1)$ of (8) carries no $\sqrt A$; the reading coincides with the printed bound for $A\ge1$, the only regime the paper uses, and no hypothesis on $c_2$ or $A$ is added
--   - generalization: a positive function $A(K,\delta)$ → $A(K(T),\delta)>0$ for $\delta\in(0,1)$ only; reason: this is all the proof reads, and a function positive everywhere satisfies it
--   - encoding: $K\ge 2$ with $K-1$ a power of two (standing, p.13) → $K=2^n+1$, indices `Fin (2^n+1)`, $\ell_K=n+1$; reason: the page assumes this throughout §§4–8; every such $K$ has this form
--   - encoding: a procedure → a deterministic adaptive program `QTree` over grid actions, with the query list from `traced`; reason: Algorithms 1, 3, 4 use no internal randomness, and a program cannot read the law; the clauses on one event are an event on (output, query list)
--   - encoding: $x^\star\in\arg\max$ → `pick` an arbitrary selection rule, applied to the set of maximizers; reason: the page allows any maximizer
--   - encoding: $O(\cdot)$ → $\exists C>0$ before all quantifiers, for all $T\ge2$; reason: Algorithm 1 requires $T\ge2$, and the proof gives a uniform constant
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), Theorem 4.2, p.15; inequality (8), p.17

import Mathlib
import Definitions.Def_BilateralProfit_Model
import Definitions.Def_BilateralProfit_QueryRoutine
import Definitions.Def_BilateralOptRegret_Model
import Definitions.Def_BilateralOptRegret_Regret
import Definitions.Def_BilateralOptRegret_Oracle
import Definitions.Def_BilateralOptRegret_Phased

namespace BilateralOptRegret

open BilateralProfit MeasureTheory

/-- **Theorem 4.2**, Castiglioni, Lunghi, Marchesi, *Optimal Regret for Profit Maximization in Bilateral Trade* (manuscript, sha256 aafed174…), p.15, with inequality (8), p.17: any refinement oracle gives the regret bound.

There is an absolute `C > 0` such that for every `T ≥ 2`, `c₁, c₂ > 0`, positive `A`, every `(c₁, c₂, A)`-refinement oracle
`Refine` at `K = K(T)`, every joint law and i.i.d. run, Algorithm 1 with the parameters (5) satisfies: if `ε⋆ < 1/8`,
`R_T ≤ 16 c₂ A(K, δ)(ε_m⁻² + K ε_m⁻¹) + 2T ε_m + 2T m δ + 2T/(K − 1)`; and always
`R_T ≤ C c₂ max(1, √A(K, δ)) T^{2/3}`.

**Formalization Note.** The second clause reads the printed `O(c₂ √A(K, δ) T^{2/3})` with `max(1, √A)`, which is the printed
bound for `A ≥ 1`, the only regime the paper uses: the term `2T/(K − 1) ≈ T^{2/3}` in (8) carries no `√A`. No hypothesis on
`c₂` or `A` is added: `c₂ ≥ 1/2` and `A(K, δ)(512 + 64K) ≥ 1` follow from the oracle definition. `A` is positive on `δ ∈ (0, 1)`,
the range Definition 4.1 uses. `Refine` and `pick` are parameters. -/
theorem theorem_4_2 :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℕ, 2 ≤ T →
      ∀ (c₁ c₂ : ℝ) (A : ℕ → ℝ → ℝ) (Refine : RefineProc (nOf T))
        (pick : Finset (Act (nOf T)) → Act (nOf T)),
        0 < c₁ → 0 < c₂ → (∀ δ : ℝ, 0 < δ → δ < 1 → 0 < A (Kof (nOf T)) δ) →
        IsRefinementOracle (nOf T) c₁ c₂ A Refine → IsSel pick →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (L : Measure (ℝ × ℝ)) (X : ℕ → Ω → ℝ × ℝ),
          IsValLaw L → IsIIDRun P X L →
          (epsStar A T < 1 / 8 →
            regret P X L (phasedPolicy A T Refine pick) T ≤
              16 * c₂ * A (Kof (nOf T)) (deltaOf T) *
                  (epsM A T ^ (-2 : ℤ) + (Kof (nOf T) : ℝ) * epsM A T ^ (-1 : ℤ)) +
                2 * (T : ℝ) * epsM A T + 2 * (T : ℝ) * (mOf A T : ℝ) * deltaOf T +
                2 * (T : ℝ) / ((Kof (nOf T) : ℝ) - 1)) ∧
          regret P X L (phasedPolicy A T Refine pick) T ≤
            C * c₂ * max 1 (Real.sqrt (A (Kof (nOf T)) (deltaOf T))) *
              (T : ℝ) ^ ((2 : ℝ) / 3) := by sorry

end BilateralOptRegret
