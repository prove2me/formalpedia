-- Prove2me | Theorems.Thm_DisentanglementImpossibility_entanglingMap_preserves_law
-- name    : DisentanglementImpossibility.entanglingMap_preserves_law
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:31:24.749005+00:00
-- url     : https://prove2.me/theorems/147b9c8f-9cca-425f-a76d-f36439d230d4
-- title:
--   Theorem 1 (proof, map $f$): $f(z)$ has the same distribution as $z$
-- statement:
--   Let $d\ge0$ be any dimension, let $z$ have a factorized density (independent coordinates $z_i\sim\mu_i$, each with a Lebesgue density), with marginal distribution functions $F_i$, and let $A$ be an orthogonal $d\times d$ matrix. Define
--
--   $$f(u)=g^{-1}\big(h^{-1}(A\,h(g(u)))\big),\qquad f_i(u)=F_i^{-1}\Big(\psi\big((A\,h(g(u)))_i\big)\Big),$$
--
--   where $F_i^{-1}$ is the quantile function of $\mu_i$. Then $f$ is measurable, $f(z)$ has the same distribution as $z$, and in particular
--
--   $$P(z\le u)=P(f(z)\le u)\qquad\text{for all }u\in\mathbb{R}^d,$$
--
--   where $\le$ is the coordinatewise order.
--
--   **Formalization Note** The paper's $g^{-1}$ is the inverse of $g$, which the paper asserts is bijective. Here $g^{-1}$ is the coordinatewise quantile map. It is defined for every factorized density and equals the inverse of $g$ when every marginal support is an interval.
-- source:
--   Locatello, Bauer, Lucic, Rätsch, Gelly, Schölkopf, Bachem, Challenging Common Assumptions in the Unsupervised Learning of Disentangled Representations, ICML 2019, arXiv:1811.12359v4, Appendix A (Proof of Theorem 1), definition of f and the sentence after it, p. 12

import Mathlib
import Definitions.Def_DisentanglementImpossibility_Basic

open MeasureTheory ProbabilityTheory

namespace DisentanglementImpossibility

theorem entanglingMap_preserves_law {d : ℕ} (μ : Fin d → Measure ℝ) (hμ : IsFactorizedDensity μ)
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A ∈ Matrix.orthogonalGroup (Fin d) ℝ) :
    Measurable (entanglingMap μ A) ∧
    (latentLaw μ).map (entanglingMap μ A) = latentLaw μ ∧
    ∀ u, latentLaw μ {z | z ≤ u} = latentLaw μ {z | entanglingMap μ A z ≤ u} := by sorry

end DisentanglementImpossibility
