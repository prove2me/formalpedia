-- Prove2me | Theorems.Thm_Arxiv2210_03613_advi_meanfield_underestimates_variance
-- name    : Arxiv2210_03613.advi_meanfield_underestimates_variance
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T16:45:49.797802+00:00
-- url     : https://prove2.me/theorems/b89df4dc-37df-43ca-8204-e35351c0c8ec
-- title:
--   Remark after eq. (9) (as proved, Gaussian target): the KL-optimal mean-field Gaussian underestimates every marginal variance
-- statement:
--   Let the target (posterior) distribution on the unconstrained space $\mathbb{R}^\iota$ be a Gaussian $p=\mathcal N(\mu_p,\Sigma)$ with $\Sigma$ positive definite. Consider the mean-field family of eq. (9),
--
--   $$q(\theta;\mu,\omega)=\mathcal N\big(\theta\mid\mu,\operatorname{diag}(e^{2\omega})\big),\qquad \mu,\omega\in\mathbb{R}^\iota.$$
--
--   Then $\mathrm{KL}[q\,\|\,p]$ attains its minimum over this family. For every minimiser $q^*$ and every coordinate $i$,
--
--   $$\operatorname{Var}_{q^*}(\theta_i)\le\operatorname{Var}_p(\theta_i).$$
--
--   The mean-field approximation obtained by minimising the KL divergence thus underestimates every marginal variance, and its marginal variances are lower bounds for those of the posterior.
--
--   **Formalization Note** This is the statement as proved. The paper gives no proof of its own: it cites Bishop (2006) and illustrates the claim with a bivariate Gaussian in Figure 1a. Both concern a Gaussian target in the space where $q$ is fitted, so that is the case stated. The paper also applies the lower bound to non-Gaussian posteriors and to the uncertainty in the original variables $m=T^{-1}(\theta)$. That wider claim is not stated. For non-Gaussian targets it is false: for $p=0.3\,\mathcal N(0,10^{-4})+0.7\,\mathcal N(0,1)$ on $\mathbb{R}$, the KL-optimal Gaussian has variance about $0.94$, while $\operatorname{Var}_p=0.70$.
-- source:
--   Zhang, Lomas, Zhou, Zheng and Curtis, 3D Bayesian Variational Full Waveform Inversion, arXiv:2210.03613v2 (2022), claim c012; Section 2.2 (ADVI), remark after eq. (9), with eq. (2) and Figure 1a, PDF p. 9; restated in Section 3.2 (p. 24), Section 4 (p. 25), Section 5 (p. 27) and the Summary (p. 2)

import Mathlib
import Definitions.Def_Arxiv2210_03613_Basic

open MeasureTheory ProbabilityTheory InformationTheory

namespace Arxiv2210_03613

theorem advi_meanfield_underestimates_variance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μp : EuclideanSpace ℝ ι) (Sig : Matrix ι ι ℝ) (hSig : Sig.PosDef) :
    (∃ (μ : EuclideanSpace ℝ ι) (ω : ι → ℝ),
      IsMeanFieldKLMin (multivariateGaussian μp Sig) μ ω) ∧
    ∀ (μ : EuclideanSpace ℝ ι) (ω : ι → ℝ),
      IsMeanFieldKLMin (multivariateGaussian μp Sig) μ ω → ∀ i : ι,
        variance (fun θ : EuclideanSpace ℝ ι => θ i) (meanFieldGaussian μ ω) ≤
          variance (fun θ : EuclideanSpace ℝ ι => θ i) (multivariateGaussian μp Sig) := by sorry

end Arxiv2210_03613
