-- Prove2me | Theorems.Thm_FTPLLinBandit_Supplement_theorem_16
-- name    : FTPLLinBandit.Supplement.theorem_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:43:28.808218+00:00
-- url     : https://prove2.me/theorems/3399bc8e-685a-492d-8c27-10ac26fdb02d
-- title:
--   Theorem 16 — bounded scalar hazard gives $\nabla^2\Psi(\Theta)\preceq2h_qM(\Theta)$ on the simplex
-- statement:
--   Let $d\ge1$ and let
--   $$
--   \Delta^d=\left\{a\in\mathbb R^d:a_i\ge0\ \text{for all }i,\ \sum_i a_i=1\right\}.
--   $$
--   Let $q$ be a probability density on $\mathbb R$, let $Q(u)=\int_{(-\infty,u]}q(s)\,ds$ be its CDF, and suppose its hazard supremum
--   $$
--   h_q=\sup_{u\in\mathbb R}\frac{q(u)}{1-Q(u)}
--   $$
--   is finite. Let $\rho(z)=\prod_i q(z_i)$ be the iid coordinate density on $\mathbb R^d$, suppose $\rho$ is regular, and let $x$ be any fixed measurable argmax selection on $\Delta^d$. If $M(\Theta)$ is the covariance of $x(\Theta+Z)$ for $Z\sim\rho$, then for every $\Theta,u\in\mathbb R^d$,
--   $$
--   u^\top\nabla^2\Psi(\Theta)u\le2h_q\,u^\top M(\Theta)u.
--   $$
--   Equivalently, $\nabla^2\Psi(\Theta)\preceq2h_qM(\Theta)$ for every $\Theta$.
--
--   This is the positive simplex counterpart to Theorem 3 and preserves the exact constant $2$.
--
--   **Formalization Note** Bounded hazard is `BddAbove` for the range of the ratio, and $h_q$ is its real `sSup`. The Hessian is the Fréchet derivative of `gradient (potential A ρ)` and action covariance is `actCovQ`.
--
--   Differences from the source:
--   - encoding: $x(\Theta)$ is the paper's arbitrary fixed argmax tie-breaking rule → $x$ is any measurable argmax selection; reason: measurability is the convention required for the displayed expectations, and every admissible fixed tie-breaking rule is covered
--   - encoding: bounded $h_q=\sup_u q(u)/(1-Q(u))$ → `BddAbove` of the nonempty ratio range and its real `sSup`, with Lean's $0/0=0$ when the survival function vanishes; reason: the boundedness guard prevents the junk value of an unbounded real supremum, and regular continuous densities vanish wherever their CDF has already reached one
--   - encoding: $\nabla^2\Psi(\Theta)\preceq2h_qM(\Theta)$ → the corresponding inequality of quadratic forms for every direction $u$, using the Fréchet derivative of the gradient; reason: symmetric matrix order is equivalent to pointwise quadratic-form order
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Theorem 16, p.24

import Mathlib
import Definitions.Def_FTPLLinBandit_IsArgmaxSel
import Definitions.Def_FTPLLinBandit_IsRegularDensity
import Definitions.Def_FTPLLinBandit_potential
import Definitions.Def_FTPLLinBandit_actCovQ

open MeasureTheory
open scoped InnerProductSpace

namespace FTPLLinBandit.Supplement

/-- **Theorem 16 (bounded hazard rate controls the FTPL Hessian on the simplex).** Wei,
*Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets*,
arXiv:2610.17818, Theorem 16, p.24.

Let `A = Δ^d` be the probability simplex. Let the perturbation density be the iid product
`ρ(z) = ∏ᵢ q(zᵢ)` of a scalar probability density `q`, and suppose that `ρ` is regular.
Writing `Q` for the CDF of `q` and `h_q = sup_u q(u)/(1-Q(u))` for its finite hazard
supremum, the Hessian of the smoothed support function is bounded at every `Θ` by exactly
`2 h_q` times the covariance of the selected action.

**Formalization Note.** `d ≥ 1`, and `Δ^d` has `d` coordinates indexed by `Fin d`. The scalar
density is explicitly nonnegative, integrable, and normalized. "Bounded hazard" is
`BddAbove` for the nonempty range of the displayed ratio; `sSup` therefore has its ordinary
real meaning rather than Lean's unbounded-set default. Division at a zero survival function
uses Lean's `0/0 = 0`; for the continuous densities covered by the regular product hypothesis,
the density is zero wherever the CDF has already reached one. The Hessian quadratic form is
the actual Fréchet derivative of `gradient (potential A ρ)`, and the inequality quantifies over
every direction, exactly expressing the matrix order. -/
theorem theorem_16 {d : ℕ} (hd : 1 ≤ d) :
    let A : Set (EuclideanSpace ℝ (Fin d)) :=
      {a | (∀ i, 0 ≤ a i) ∧ ∑ i, a i = 1}
    ∀ (x : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)), IsArgmaxSel A x →
      ∀ q : ℝ → ℝ, (∀ s, 0 ≤ q s) → Integrable q → ∫ s, q s = 1 →
        let Q : ℝ → ℝ := fun t => ∫ s in Set.Iic t, q s
        let hazard : ℝ → ℝ := fun t => q t / (1 - Q t)
        BddAbove (Set.range hazard) →
          let hq : ℝ := sSup (Set.range hazard)
          let ρ : EuclideanSpace ℝ (Fin d) → ℝ := fun z => ∏ i, q (z i)
          IsRegularDensity ρ →
            ∀ (Θ u : EuclideanSpace ℝ (Fin d)),
              ⟪u, (fderiv ℝ (gradient (potential A ρ)) Θ) u⟫_ℝ ≤
                2 * hq * actCovQ x ρ Θ u := by sorry

end FTPLLinBandit.Supplement
