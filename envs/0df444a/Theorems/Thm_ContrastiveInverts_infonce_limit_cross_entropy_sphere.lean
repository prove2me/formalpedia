-- Prove2me | Theorems.Thm_ContrastiveInverts_infonce_limit_cross_entropy_sphere
-- name    : ContrastiveInverts.infonce_limit_cross_entropy_sphere
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:41:45.551594+00:00
-- url     : https://prove2.me/theorems/4d28a8f5-5ce3-4c43-9923-544457716975
-- title:
--   Theorem 1: $\mathcal{L}_\mathsf{contr}$ converges to the cross-entropy between latent distributions
-- statement:
--   Let $N\ge1$, $N\le K$, and let the latents lie on $Z=\mathbb{S}^{N-1}$ with uniform marginal and von Mises–Fisher conditional $p(\tilde z\mid z)=C_p^{-1}e^{\kappa z^\top\tilde z}$, $\kappa>0$. Let $g$ map $Z$ injectively into the observation space $\mathcal{X}\subseteq\mathbb{R}^K$, and let $g$ be differentiable on an open neighbourhood of $Z$. Let the encoder $f$ map $\mathcal{X}$ into the sphere of radius $r>0$, and let $h=f\circ g$ be measurable on $Z$. Then, for every $\tau>0$,
--
--   $$\lim_{M\to\infty}\Big(\mathcal{L}_{\mathsf{contr}}(f;\tau,M)-\log M+\log|Z|\Big)=\mathbb{E}_{z\sim p(z)}\big[H\big(p(\cdot\mid z),q_h(\cdot\mid z)\big)\big],$$
--
--   where $|Z|$ is the surface area of $\mathbb{S}^{N-1}$ and $q_h(\tilde z\mid z)=C_h(z)^{-1}e^{h(\tilde z)^\top h(z)/\tau}$.
--
--   So, up to a constant, the InfoNCE objective with many negatives is the cross-entropy between the true conditional of positive pairs and the conditional that the encoder induces on the latents.
--
--   **Formalization Note** The loss is written on latents: a positive pair of observations is $(g(z),g(\tilde z))$ and the negatives are $g(z_i^-)$, so $f(x)^\top f(\tilde x)=h(z)^\top h(\tilde z)$. The standing assumptions of Appendix A.1.1 (injectivity and differentiability of $g$, model sphere of radius $r$) are included although the limit uses only the boundedness and measurability of $h$. Measurability of $h$ is the standing convention that makes the expectations defined.
-- source:
--   Zimmermann, Sharma, Schneider, Bethge and Brendel, Contrastive Learning Inverts the Data Generating Process, ICML 2021, arXiv:2102.08850v4, Section 3.1, Theorem 1, eqs. (1)-(4), p. 3; restated with proof in Appendix A.1.2, pp. 13-14; standing assumptions of Appendix A.1.1, p. 13

import Mathlib
import Definitions.Def_ContrastiveInverts_Basic

open MeasureTheory Filter Topology

namespace ContrastiveInverts

theorem infonce_limit_cross_entropy_sphere {N K : ℕ} (hN : 0 < N) (hNK : N ≤ K)
    (τ κ r : ℝ) (hτ : 0 < τ) (hκ : 0 < κ) (hr : 0 < r)
    (X : Set (Vec K)) (g : Vec N → Vec K) (hgX : ∀ z ∈ Metric.sphere (0 : Vec N) 1, g z ∈ X)
    (hg_inj : Set.InjOn g (Metric.sphere (0 : Vec N) 1))
    (hg_diff : ∃ U : Set (Vec N), IsOpen U ∧ Metric.sphere (0 : Vec N) 1 ⊆ U ∧
      DifferentiableOn ℝ g U)
    (f : Vec K → Vec N) (hf : ∀ x ∈ X, f x ∈ Metric.sphere (0 : Vec N) r)
    (hmeas : Measurable (fun z : Sph N => f (g z))) :
    Tendsto (fun M : ℕ => infoNCE κ τ (f ∘ g) M - Real.log M + Real.log (sphereArea N)) atTop
      (𝓝 (sphCrossEntropy κ τ (f ∘ g))) := by sorry

end ContrastiveInverts
