-- Prove2me | Theorems.Thm_BERicci_Energy_theorem_3_12_energy
-- name    : BERicci.Energy.theorem_3_12_energy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:33:38.627308+00:00
-- url     : https://prove2.me/theorems/f1b36219-00ed-4503-afa0-88280f864ac0
-- title:
--   Theorem 3.12 (second part), p. 36 — under (MD) and (ED.b): 2Ch ≥ E (3.33), D(Ch) ⊂ 𝔾 ⊂ 𝕍 and |Dg|²_w ≥ Γ(g) (3.34)
-- statement:
--   Let $\mathcal E$ be a strongly local symmetric Dirichlet form on $L^2(X,m)$ satisfying (2.1), and let $d$ be a distance on $X$ satisfying (MD) and (ED.b). Let $\mathrm{Ch}$ be the Cheeger energy of $(X,d,m)$ and $|Dg|_w$ the minimal weak gradient. Then
--
--   $$2\,\mathrm{Ch}(g)\ge\mathcal E(g)\qquad\text{for every }g\in L^2(X,m),\tag{3.33}$$
--
--   $$D(\mathrm{Ch})\subset\mathbb G\subset\mathbb V,\qquad |Dg|_w^2\ge\Gamma(g)\quad m\text{-a.e., for every }g\in D(\mathrm{Ch}),\tag{3.34}$$
--
--   where $D(\mathrm{Ch})=\{g:\mathrm{Ch}(g)<\infty\}$.
--
--   This is the inequality between the Dirichlet form and twice the Cheeger energy that holds as soon as Lipschitz functions of slope at most one are admissible competitors in $\mathbb L_C$. Theorem 3.14 identifies when it is an equality.
--
--   **Formalization Note** $d$ is the metric of $X$; (MD.a)'s completeness, separability and Borel σ-algebra are binders. $\mathbb G\subset\mathbb V$ holds by the definition of $\mathbb G$ (a carré du champ density is only assigned to $f$ with $\mathcal E(f)<\infty$) and is not restated. The existence of $|Dg|_w$ for $g\in D(\mathrm{Ch})$, recalled on p. 24 and presupposed by (3.34), is stated explicitly. The inequality $|Dg|_w^2\ge\Gamma(g)$ is stated for every carré du champ density of $g$ and every minimal weak gradient of $g$ (both unique $m$-a.e.).
-- source:
--   arXiv:1209.5786v4, Theorem 3.12 (second sentence), (3.33), (3.34), p. 36

import Mathlib
import Definitions.Def_BERicci_Gamma_Setting
import Definitions.Def_BERicci_Energy_Conditions

namespace BERicci.Energy

open MeasureTheory Filter Topology
open scoped ENNReal

/-- **Theorem 3.12** (p. 36), second part: under (MD) and (ED.b), `2 Ch(g) ≥ E(g)` on `L²(X, m)` (3.33), and
`D(Ch) ⊂ 𝔾 ⊂ 𝕍` with `|Dg|_w² ≥ Γ(g)` m-a.e. for `g ∈ D(Ch)` (3.34); the existence of `|Dg|_w`
for `g ∈ D(Ch)` (p. 24) is made explicit. -/
theorem theorem_3_12_energy {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    (m : Measure X) (E : (X → ℝ) → ℝ≥0∞) (hE : BERicci.Gamma.IsDirichletForm m E) (hloc : BERicci.Gamma.IsStronglyLocal m E)
    (hMD : MD m) (hEDb : EDb m E) :
    (∀ g : X → ℝ, MemLp g 2 m → E g ≤ 2 * BERicci.Gamma.cheeger m g) ∧
    (∀ g : X → ℝ, BERicci.Gamma.cheeger m g < ⊤ →
      (∃ γ : X → ℝ, BERicci.Gamma.IsCarreDuChamp m E g γ) ∧ (∃ w : X → ℝ, IsMinWeakGrad m g w) ∧
      ∀ γ w : X → ℝ, BERicci.Gamma.IsCarreDuChamp m E g γ → IsMinWeakGrad m g w →
        γ ≤ᵐ[m] fun x => w x ^ 2) := by sorry

end BERicci.Energy
