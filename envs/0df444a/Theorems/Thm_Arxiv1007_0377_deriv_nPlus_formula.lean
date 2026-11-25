-- Prove2me | Theorems.Thm_Arxiv1007_0377_deriv_nPlus_formula
-- name    : Arxiv1007_0377.deriv_nPlus_formula
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T00:01:28.290787+00:00
-- url     : https://prove2.me/theorems/1978a479-5509-4b32-a5a4-2c57760aaa78
-- title:
--   Eq. for $\partial n_+/\partial\omega$ (after eq. (5)): the frequency derivative of $n_+$
-- statement:
--   Let $\epsilon,\mu:\mathbb{R}\to\mathbb{C}$ be the permittivity and permeability as functions of the real frequency $\omega$, both differentiable at $\omega$, and write $'=d/d\omega$. Let $R(\omega)=\epsilon_r\mu_r-\epsilon_i\mu_i+|\epsilon||\mu|$ and suppose $R(\omega)>0$. Then $n_+(\omega)=\sqrt{R(\omega)}/\sqrt2$ is differentiable at $\omega$, with
--
--   $$\frac{\partial n_+}{\partial\omega}=\frac{1}{\sqrt2}\frac12\left(\frac{\epsilon_r'\mu_r+\epsilon_r\mu_r'-(\epsilon_i'\mu_i+\epsilon_i\mu_i')}{\sqrt{\epsilon_r\mu_r-\epsilon_i\mu_i+|\epsilon||\mu|}}\right)+\frac{1}{\sqrt2}\frac12\left(\frac{|\epsilon|'|\mu|+|\epsilon||\mu|'}{\sqrt{\epsilon_r\mu_r-\epsilon_i\mu_i+|\epsilon||\mu|}}\right).$$
--
--   The paper reads this formula as showing where the branch $n_+$ can stop being smooth: only where the radicand vanishes.
--
--   **Formalization Note** The paper writes the formula without hypotheses. The statement assumes that $\epsilon$ and $\mu$ are differentiable at $\omega$ and that $R(\omega)>0$, which the formula needs because it divides by $\sqrt{R}$. $R(\omega)>0$ forces $\epsilon(\omega)\neq0$ and $\mu(\omega)\neq0$, so $|\epsilon|$ and $|\mu|$ are differentiable at $\omega$. The paper's further claims, that $n_+$ has a divergent derivative where $R=0$ and that the branches $(n_\pm,\kappa_\pm)$ violate the Kramers–Kronig relations, are not part of this statement.
-- source:
--   Hickey, Akyurtlu and Kussow, Relationship between the Kramers-Kronig relations and negative index of refraction, arXiv:1007.0377v2 (2010), claim c003 (part (i)); main text, unnumbered display between Fig. 1 and eq. (6), PDF p. 2

import Mathlib
import Definitions.Def_Arxiv1007_0377_Basic

open Complex Polynomial

namespace Arxiv1007_0377

theorem deriv_nPlus_formula (ε μ : ℝ → ℂ) (ω : ℝ)
    (hε : DifferentiableAt ℝ ε ω) (hμ : DifferentiableAt ℝ μ ω)
    (hR : 0 < branchRadicand (ε ω) (μ ω)) :
    HasDerivAt (fun w => nPlus (ε w) (μ w))
      (1 / Real.sqrt 2 * (1 / 2) *
          (((deriv ε ω).re * (μ ω).re + (ε ω).re * (deriv μ ω).re -
              ((deriv ε ω).im * (μ ω).im + (ε ω).im * (deriv μ ω).im)) /
            Real.sqrt (branchRadicand (ε ω) (μ ω))) +
        1 / Real.sqrt 2 * (1 / 2) *
          ((deriv (fun w => ‖ε w‖) ω * ‖μ ω‖ + ‖ε ω‖ * deriv (fun w => ‖μ w‖) ω) /
            Real.sqrt (branchRadicand (ε ω) (μ ω)))) ω := by sorry

end Arxiv1007_0377
