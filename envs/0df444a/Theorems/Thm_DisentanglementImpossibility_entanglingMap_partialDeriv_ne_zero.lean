-- Prove2me | Theorems.Thm_DisentanglementImpossibility_entanglingMap_partialDeriv_ne_zero
-- name    : DisentanglementImpossibility.entanglingMap_partialDeriv_ne_zero
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:31:49.778807+00:00
-- url     : https://prove2.me/theorems/ecba871c-b099-4c1d-91e8-19106f22a554
-- title:
--   Theorem 1 (proof, Jacobian of $f$): every partial derivative of $f$ is nonzero almost everywhere
-- statement:
--   Let $d\ge0$ be any dimension, let $z\sim P$ have a factorized density (independent coordinates $z_i\sim\mu_i$, each with a Lebesgue density), let $A$ be an orthogonal $d\times d$ matrix with $A_{ij}\ne0$ for all $i,j$, and let $f(u)=g^{-1}(h^{-1}(A\,h(g(u))))$ be the entangling map, with $g^{-1}$ the coordinatewise quantile map. Then for all $i,j\in\{1,\dots,d\}$ and $P$-almost every $u$, the partial derivative
--
--   $$\frac{\partial f_i(u)}{\partial u_j}$$
--
--   exists and is nonzero.
--
--   This is the last display of the proof of Theorem 1: $\partial f_i/\partial u_j$ is $A_{ij}$ times a product of derivatives of $g$, $h$ and their inverses.
--
--   **Formalization Note** "Almost every $u\in\operatorname{supp}(z)$" is read with respect to $P$. The partial derivative is the derivative of the map $t\mapsto f_i(u_1,\dots,t,\dots,u_d)$, which is defined for all real $t$.
-- source:
--   Locatello, Bauer, Lucic, Rätsch, Gelly, Schölkopf, Bachem, Challenging Common Assumptions in the Unsupervised Learning of Disentangled Representations, ICML 2019, arXiv:1811.12359v4, Appendix A (Proof of Theorem 1), final display, p. 12

import Mathlib
import Definitions.Def_DisentanglementImpossibility_Basic

open MeasureTheory ProbabilityTheory

namespace DisentanglementImpossibility

theorem entanglingMap_partialDeriv_ne_zero {d : ℕ} (μ : Fin d → Measure ℝ)
    (hμ : IsFactorizedDensity μ) (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin d) ℝ) (hA0 : ∀ i j, A i j ≠ 0) :
    ∀ i j, ∀ᵐ u ∂(latentLaw μ), partialDeriv (entanglingMap μ A) i j u ≠ 0 := by sorry

end DisentanglementImpossibility
