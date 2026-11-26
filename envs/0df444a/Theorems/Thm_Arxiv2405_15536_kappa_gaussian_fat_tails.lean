-- Prove2me | Theorems.Thm_Arxiv2405_15536_kappa_gaussian_fat_tails
-- name    : Arxiv2405_15536.kappa_gaussian_fat_tails
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T18:16:56.529772+00:00
-- url     : https://prove2.me/theorems/e968056d-6787-4b7a-88e4-8734a2590fb2
-- title:
--   Eq. (6), Fig. 1(a)-(b): the $\kappa$-Gaussian has power-law (fat) tails, heavier as $\kappa$ grows
-- statement:
--   Let $0<\kappa<2/3$. Then the κ-Gaussian has a power-law tail:
--
--   $$\exp_\kappa(-\beta_\kappa\varepsilon^2)\sim\big(2\kappa\beta_\kappa\varepsilon^2\big)^{-1/\kappa}\qquad(|\varepsilon|\to\infty),$$
--
--   so $p_\kappa(\varepsilon)$ decays like $|\varepsilon|^{-2/\kappa}$. In particular:
--
--   1. its tails are heavier than Gaussian: $p_\kappa(\varepsilon)/p_0(\varepsilon)\to+\infty$ as $|\varepsilon|\to\infty$;
--   2. the tails become heavier as $\kappa$ increases: for every $\kappa'$ with $\kappa<\kappa'<2/3$, $p_{\kappa'}(\varepsilon)/p_\kappa(\varepsilon)\to+\infty$ as $|\varepsilon|\to\infty$.
--
--   This is the precise content of the paper's remark that fat tails appear as $\kappa$ increases.
--
--   **Formalization Note** The paper states the remark without the qualifier $|\varepsilon|\to\infty$; at finite $\varepsilon$ it fails (for instance $p_{0.6}(3)/p_0(3)\approx0.81$), so the statement is the asymptotic one. Asymptotic equivalence is Mathlib's `IsEquivalent` along the cocompact filter of $\mathbb{R}$, which is the filter $|\varepsilon|\to\infty$. The paper's following sentence about the "weight" given to small and large errors is not included.
-- source:
--   da Silva and Kaniadakis, A graph-space optimal transport FWI approach based on kappa-generalized Gaussian distribution, arXiv:2405.15536v1 (2024), claim c012; Sec. 2.2, discussion of Fig. 1(a)-(b), eqs. (6)-(9), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv2405_15536_Basic

open MeasureTheory Filter Topology Asymptotics

namespace Arxiv2405_15536

theorem kappa_gaussian_fat_tails (κ : ℝ) (hκ0 : 0 < κ) (hκ : κ < 2 / 3) :
    IsEquivalent (cocompact ℝ) (fun ε => expKappa κ (-betaKappa κ * ε ^ 2))
      (fun ε => (2 * κ * betaKappa κ * ε ^ 2) ^ (-1 / κ)) ∧
    Tendsto (fun ε => kappaGaussian κ ε / ProbabilityTheory.gaussianPDFReal 0 1 ε)
      (cocompact ℝ) atTop ∧
    (∀ κ' : ℝ, κ < κ' → κ' < 2 / 3 →
      Tendsto (fun ε => kappaGaussian κ' ε / kappaGaussian κ ε) (cocompact ℝ) atTop) := by sorry

end Arxiv2405_15536
