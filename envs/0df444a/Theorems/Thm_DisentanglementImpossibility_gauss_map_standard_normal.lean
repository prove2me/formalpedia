-- Prove2me | Theorems.Thm_DisentanglementImpossibility_gauss_map_standard_normal
-- name    : DisentanglementImpossibility.gauss_map_standard_normal
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:29:48.066274+00:00
-- url     : https://prove2.me/theorems/e8cd6e5e-c4e1-43d1-9a3e-2b344706ed1e
-- title:
--   Theorem 1 (proof, map $h$): $h(g(z))$ is standard normal
-- statement:
--   Let $\psi$ be the standard normal distribution function and $h(v)=(\psi^{-1}(v_1),\dots,\psi^{-1}(v_d))$. Then:
--
--   1. $h$ is a bijection from $(0,1)^d$ onto $\mathbb{R}^d$;
--   2. $(\psi^{-1})'(x)$ exists and is nonzero for every $x\in(0,1)$, so $\partial h_i/\partial v_i\ne0$ on $(0,1)^d$;
--   3. if $z$ has a factorized density (in any dimension $d$) and $g$ is its coordinatewise distribution-function map, then $h(g(z))$ has the $d$-dimensional standard normal distribution $N(0,I_d)$.
--
--   **Formalization Note** The paper defines $h$ on $(0,1]^d$, but $\psi^{-1}(1)$ is not a real number. The bijection is stated on the open cube $(0,1)^d$. The boundary of the cube has probability zero under the law of $g(z)$. The paper also says $\partial h_i/\partial v_j=0$ for $i\ne j$. That holds trivially, because $h_i$ depends only on $v_i$, and it is not part of the formal statement.
-- source:
--   Locatello, Bauer, Lucic, Rätsch, Gelly, Schölkopf, Bachem, Challenging Common Assumptions in the Unsupervised Learning of Disentangled Representations, ICML 2019, arXiv:1811.12359v4, Appendix A (Proof of Theorem 1), definition of h and the two sentences after it, p. 12

import Mathlib
import Definitions.Def_DisentanglementImpossibility_Basic

open MeasureTheory ProbabilityTheory

namespace DisentanglementImpossibility

theorem gauss_map_standard_normal {d : ℕ} (μ : Fin d → Measure ℝ) (hμ : IsFactorizedDensity μ) :
    Set.BijOn (gaussMap (d := d)) (Set.univ.pi fun _ => Set.Ioo 0 1) Set.univ ∧
    (∀ x ∈ Set.Ioo (0 : ℝ) 1, deriv stdNormalQuantile x ≠ 0) ∧
    (latentLaw μ).map (fun u => gaussMap (cdfMap μ u)) = stdGaussian d := by sorry

end DisentanglementImpossibility
