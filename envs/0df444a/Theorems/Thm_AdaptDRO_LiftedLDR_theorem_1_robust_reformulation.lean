-- Prove2me | Theorems.Thm_AdaptDRO_LiftedLDR_theorem_1_robust_reformulation
-- name    : AdaptDRO.LiftedLDR.theorem_1_robust_reformulation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T18:48:26.349396+00:00
-- url     : https://prove2.me/theorems/4a22890a-982e-486c-be50-075b07b9f640
-- title:
--   Theorem 1 — robust reformulation of worst-case recourse cost
-- statement:
--   Let $x\in X$, and suppose the recourse LP is feasible for every $x\in X$ and $z\in W$. Assume Definition 3's SOC model and Assumption 1's lifted-support representation and Slater point. Then the distributionally robust value equals the value of robust program (9):
--
--   $$
--   \beta(x)=\inf_{\substack{r\in\mathbb R,\ s\in\mathbb R^{L_1},\ t\in\mathbb R^{I_2}_+\\r+s^\top Gz+t^\top u\ge Q(x,z)\ \forall(z,u)\in\bar W}}
--      \bigl(r+s^\top\mu+t^\top\sigma\bigr).
--   $$
--
--   The formula replaces optimization over an ambiguity set of distributions with robust inequalities on a lifted SOC support. It is the first displayed reformulation in Theorem 1; the paper's subsequent finite-dimensional conic form (10) is not asserted here.
--
--   **Formalization Note** Dual feasibility of the recourse LP is explicit so $Q(x,z)$ is finite. Both sides take values in the extended reals. The paper writes “min” for (9); Lean states its infimum and makes no attainment claim. The SOC support and every epigraph are carried as standing assumptions.
-- source:
--   Bertsimas, Sim, Zhang, Adaptive distributionally robust optimization, Management Science 65(2) (2019), p. 608, Theorem 1, Eq. (9), Assumption 1

import Mathlib
import Definitions.Def_AdaptDRO_LiftedLDR_Model

namespace AdaptDRO.LiftedLDR

/-- Theorem 1 (p. 608), first formulation (9): moment DRO duality over the
SOC lifted support. -/
theorem theorem_1_robust_reformulation
    {I1 I2 I3 L1 L2 M N1 N2 : ℕ} (m : Model I1 I2 L1 M N1 N2)
    (X : Set (Fin N1 → ℝ))
    (C : Matrix (Fin L2) (Fin I1) ℝ)
    (D : Matrix (Fin L2) (Fin I2) ℝ)
    (E : Matrix (Fin L2) (Fin I3) ℝ)
    (h : Fin L2 → ℝ) (K : Set (Fin L2 → ℝ))
    (hSOC : m.SOCData) (hAssumption1 : m.Assumption1 C D E h K)
    (hrec : m.RelativelyComplete X) (hdual : m.recourse.DualFeasible)
    (x : Fin N1 → ℝ) (hx : x ∈ X) :
    m.beta x = m.robustValue9 x := by sorry

end AdaptDRO.LiftedLDR
