-- Prove2me | Theorems.Thm_DisentanglementImpossibility_orthogonal_map_std_gaussian
-- name    : DisentanglementImpossibility.orthogonal_map_std_gaussian
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:30:49.106568+00:00
-- url     : https://prove2.me/theorems/be882d6f-0ec6-4681-bddc-02c903742dd8
-- title:
--   Theorem 1 (proof, rotation): an orthogonal matrix preserves the standard normal law
-- statement:
--   Let $A$ be an orthogonal $d\times d$ real matrix and let $x$ have the $d$-dimensional standard normal distribution $N(0,I_d)$. Then $Ax$ also has the distribution $N(0,I_d)$:
--
--   $$A_\#N(0,I_d)=N(0,I_d).$$
--
--   In the proof of Theorem 1 this is applied to $x=h(g(z))$, because the covariance matrix of $Ax$ is $AA^\top=I_d$.
-- source:
--   Locatello, Bauer, Lucic, Rätsch, Gelly, Schölkopf, Bachem, Challenging Common Assumptions in the Unsupervised Learning of Disentangled Representations, ICML 2019, arXiv:1811.12359v4, Appendix A (Proof of Theorem 1), sentence 'The random variable Ah(g(z)) ... is hence an independent, multivariate standard normal distribution', p. 12

import Mathlib
import Definitions.Def_DisentanglementImpossibility_Basic

open MeasureTheory ProbabilityTheory

namespace DisentanglementImpossibility

theorem orthogonal_map_std_gaussian {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin d) ℝ) :
    (stdGaussian d).map (fun x => A.mulVec x) = stdGaussian d := by sorry

end DisentanglementImpossibility
