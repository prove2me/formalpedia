-- Prove2me | Theorems.Thm_CCPCollateral_Incentive_lemma_IA_1
-- name    : CCPCollateral.Incentive.lemma_IA_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:22:16.733897+00:00
-- url     : https://prove2.me/theorems/b8397f33-0478-4186-a2f8-dad52c49562a
-- title:
--   Lemma IA.1, p. OA-1 — explicit expression (A28), positivity, strict decrease in g, I and F, piecewise linearity, continuity and boundary value of X^g
-- statement:
--   Work in the model of the setting under the standing assumptions, and fix a number $g\le N-1$ of other members who hedge. Let $X^g(I,F)$ be the expected loss-sharing contribution and financing cost of a surviving member,
--   $$X^g(I,F)=\sum_{k=0}^{N-1}f^g(k)\left[\frac{k(D-I-F)}{N-k}+\alpha\Bigl(\frac{k(D-I-F)}{N-k}-F\Bigr)^+\right].$$
--   Its explicit expression (A28), for $I,F\ge0$ and $I+F<D$, is
--   $$X^g(I,F)=\sum_{k=0}^{N-1} f^g(k)\frac{k(D-I-F)}{N-k}+\alpha\sum_{k=\lceil NF/(D-I)\rceil}^{N-1}f^g(k)\frac{k(D-I)-NF}{N-k}.$$
--   Then:
--   1. $X^g(I,F)>0$ whenever $I,F\ge0$ and $I+F<D$;
--   2. $X^g$ is strictly decreasing in $g$: $X^{g'}(I,F)<X^g(I,F)$ for $g<g'\le N-1$, $I,F\ge 0$, $I+F<D$;
--   3. for fixed $F\ge0$, $I\mapsto X^g(I,F)$ is strictly decreasing on $\{I\ge0:\ I+F\le D\}$; for fixed $I\in[0,D)$, $F\mapsto X^g(I,F)$ is strictly decreasing on $\{F\ge 0:\ I+F\le D\}$;
--   4. $(I,F)\mapsto X^g(I,F)$ is continuous;
--   5. $X^g$ is piecewise linear: for $I<D$ it is affine in $F$ on every cell $l(D-I)/N\le F\le(l+1)(D-I)/N$, and for $F\ge 0$ it is affine in $I$ on every cell $\{I<D:\ l(D-I)\le NF\le(l+1)(D-I)\}$ ($l=0,1,2,\dots$), i.e. wherever $\lceil NF/(D-I)\rceil$ is constant;
--   6. $X^g(I,D-I)=0$ for $I\le D$.
--
--   These are the properties of the loss-sharing cost on which the equilibrium analysis of Proposition 2 rests: monotonicity in $g$ makes hedging a strategic complement, and monotonicity in $F$ makes the hedging cutoff unique.
--
--   **Formalization Note** The page states the properties "for $I+F<D$"; monotonicity in $I$ and $F$ is stated on the closed region up to $I+F=D$, where $X^g=0$. "Piecewise linear" is rendered as affinity on the cells where $\lceil NF/(D-I)\rceil$ is constant; the page's "$X^g(I;D-I)=0$" is read as $X^g(I,D-I)=0$.
-- source:
--   Wang, Capponi & Zhang, A Theory of Collateral Requirements for Central Counterparties, author's manuscript (2021; Management Sci. doi:10.1287/mnsc.2021.4145), Online Appendix, Lemma IA.1, p. OA-1

import Mathlib
import Definitions.Def_CCPCollateral_Incentive_Setting

namespace CCPCollateral.Incentive

/-- Lemma IA.1 (p. OA-1): the ceiling-sum expression (A28) for `X^g`, its positivity,
strict decrease in `g`, `I`, and `F`, continuity, piecewise linearity, and the boundary value
`X^g(I, D − I) = 0`. -/
theorem lemma_IA_1 (m : Params) (hm : Standing m) (g : ℕ) (hg : g ≤ m.N - 1) :
    (∀ I F : ℝ, 0 ≤ I → 0 ≤ F → I + F < m.D →
      m.X g I F =
        (∑ k ∈ Finset.range m.N, m.defaultLaw g k *
          ((k : ℝ) * (m.D - I - F) / ((m.N : ℝ) - k))) +
        (∑ k ∈ (Finset.range m.N).filter
          (fun k => ⌈(m.N : ℝ) * F / (m.D - I)⌉₊ ≤ k),
          m.defaultLaw g k * m.α *
            (((k : ℝ) * (m.D - I) - m.N * F) / ((m.N : ℝ) - k)))) ∧
    (∀ I F : ℝ, 0 ≤ I → 0 ≤ F → I + F < m.D → 0 < m.X g I F) ∧
    (∀ g' : ℕ, g < g' → g' ≤ m.N - 1 → ∀ I F : ℝ, 0 ≤ I → 0 ≤ F → I + F < m.D →
      m.X g' I F < m.X g I F) ∧
    (∀ F : ℝ, 0 ≤ F → StrictAntiOn (fun I => m.X g I F) {I | 0 ≤ I ∧ I + F ≤ m.D}) ∧
    (∀ I : ℝ, 0 ≤ I → I < m.D → StrictAntiOn (fun F => m.X g I F) {F | 0 ≤ F ∧ I + F ≤ m.D}) ∧
    Continuous (fun p : ℝ × ℝ => m.X g p.1 p.2) ∧
    (∀ I : ℝ, I < m.D → ∀ l : ℕ, ∃ u v : ℝ,
      ∀ F ∈ Set.Icc ((l : ℝ) * (m.D - I) / m.N) (((l : ℝ) + 1) * (m.D - I) / m.N),
        m.X g I F = u * F + v) ∧
    (∀ F : ℝ, 0 ≤ F → ∀ l : ℕ, ∃ u v : ℝ, ∀ I : ℝ, I < m.D →
      (l : ℝ) * (m.D - I) ≤ (m.N : ℝ) * F → (m.N : ℝ) * F ≤ ((l : ℝ) + 1) * (m.D - I) →
        m.X g I F = u * I + v) ∧
    (∀ I : ℝ, I ≤ m.D → m.X g I (m.D - I) = 0) := by sorry

end CCPCollateral.Incentive
