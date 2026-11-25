-- Prove2me | Theorems.Thm_Arxiv1606_00062_remark12_spectral_radius_bound
-- name    : Arxiv1606_00062.remark12_spectral_radius_bound
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T22:42:50.767703+00:00
-- url     : https://prove2.me/theorems/8417f17f-91ef-426b-8981-bf121c8a688c
-- title:
--   Remark 12: the bound (47) gives $r(\mathcal K)\le\delta<1$
-- statement:
--   Let $E$ be a complex Banach space and $\mathcal K:E\to E$ a bounded linear operator. Suppose there are constants $C>0$ and $\delta\in(0,1)$ such that the inequality (47),
--
--   $$\|\mathcal K^\ell h\|\le C\,\delta^\ell\,\|h\|,$$
--
--   holds for all integers $\ell\ge1$ and all $h\in E$. Then
--
--   $$r(\mathcal K)=\lim_{\ell\to\infty}\|\mathcal K^\ell\|^{1/\ell}\le\delta<1.$$
--
--   In the paper $E=C(\partial\Omega)$ with the supremum norm and $\mathcal K$ is the Kirchhoff operator of Section 6, so that Theorem 8 applies to it.
--
--   **Formalization Note** The implication from (47) to the bound on the spectral radius is stated for every bounded operator on every complex Banach space; the bound (47) itself (Theorem 11) is a hypothesis, as it is in the Remark. The paper's $\ell\in\mathbb Z_+$ may or may not include $\ell=0$; the hypothesis is required only for $\ell\ge1$, which covers both readings. The spectral radius is an extended nonnegative real, so $\delta$ enters as $\max(\delta,0)=\delta$ in $[0,\infty]$ and the limit is taken of $\|\mathcal K^\ell\|^{1/\ell}$ in $[0,\infty]$.
-- source:
--   Boubendir, Ecevit and Reitich, Acceleration of an iterative method for the evaluation of high-frequency multiple scattering effects, arXiv:1606.00062v1 (2016), claim c013; Section 6, Remark 12, using eq. (47) of Theorem 11, PDF p. 16

import Mathlib
import Definitions.Def_Arxiv1606_00062_Basic

open Filter Topology

namespace Arxiv1606_00062

theorem remark12_spectral_radius_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (K : E →L[ℂ] E) (C δ : ℝ) (hC : 0 < C) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (h47 : ∀ l : ℕ, 1 ≤ l → ∀ h : E, ‖(K ^ l) h‖ ≤ C * δ ^ l * ‖h‖) :
    Tendsto (fun l : ℕ => ENNReal.ofReal (‖K ^ l‖ ^ (1 / (l : ℝ)))) atTop
      (𝓝 (spectralRadius ℂ K)) ∧
    spectralRadius ℂ K ≤ ENNReal.ofReal δ ∧
    spectralRadius ℂ K < 1 := by sorry

end Arxiv1606_00062
