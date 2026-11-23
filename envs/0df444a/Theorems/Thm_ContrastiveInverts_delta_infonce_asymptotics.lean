-- Prove2me | Theorems.Thm_ContrastiveInverts_delta_infonce_asymptotics
-- name    : ContrastiveInverts.delta_infonce_asymptotics
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:44:52.821127+00:00
-- url     : https://prove2.me/theorems/20a7ced9-d3ba-453b-8bf1-6aa76c0506dc
-- title:
--   Proposition 3: asymptotics of $\mathcal{L}_{\delta\text{-contr}}$ as the number of negatives grows
-- statement:
--   Let $Z$ and $Z'$ be convex bodies in $\mathbb{R}^N$, $N\le K$, $\lambda>0$ and $\tau>0$. Let $\delta$ be a metric induced by a norm, or a semi-metric $j\circ\delta'$ of such a metric. Let positive pairs be drawn as $z\sim p(z)=|Z|^{-1}$, $\tilde z\sim p(\tilde z\mid z)=C_p(z)^{-1}e^{-\lambda\delta(\tilde z,z)}$. Let $g$ map $Z$ injectively into $\mathcal X\subseteq\mathbb{R}^K$, let the encoder $f$ map $\mathcal X$ into $Z'$, and let $h=f\circ g$ be measurable on $Z$. Then
--
--   $$\lim_{M\to\infty}\Big(\mathcal{L}_{\delta\text{-contr}}(f;\tau,M)-\log M\Big)=\mathcal{L}_{\delta\text{-align}}(f;\tau)+\mathcal{L}_{\delta\text{-unif}}(f;\tau),$$
--
--   where $\mathcal{L}_{\delta\text{-align}}(f;\tau)=\frac1\tau\mathbb{E}_{z\sim p(z),\,\tilde z\sim p(\tilde z\mid z)}\,\delta(h(\tilde z),h(z))$ and $\mathcal{L}_{\delta\text{-unif}}(f;\tau)=\mathbb{E}_{z\sim p(z)}\log\mathbb{E}_{\tilde z\sim p(\tilde z)}e^{-\delta(h(\tilde z),h(z))/\tau}$, with $p(\tilde z)$ the uniform marginal.
--
--   This is the convex-body analogue of the alignment–uniformity decomposition of Wang and Isola (2020).
--
--   **Formalization Note** The standing assumptions of Appendix A.2.1 are included: $Z$ and $Z'$ are convex bodies, $g$ is injective on $Z$, $K\ge N$, $\lambda>0$. Following eq. (5), $\delta$ is induced by a norm, which makes it continuous.
-- source:
--   Zimmermann, Sharma, Schneider, Bethge and Brendel, Contrastive Learning Inverts the Data Generating Process, ICML 2021, arXiv:2102.08850v4, Appendix A.2.2, Proposition 3, p. 15 (proof pp. 15-16); Definition 1, eq. (6), p. 5; standing assumptions of Appendix A.2.1, p. 15

import Mathlib
import Definitions.Def_ContrastiveInverts_Basic

open MeasureTheory Filter Topology

namespace ContrastiveInverts

theorem delta_infonce_asymptotics {N K : ℕ} (hNK : N ≤ K) (Z Z' : Set (Vec N))
    (hZ : IsConvexBody Z) (hZ' : IsConvexBody Z') (lam τ : ℝ) (hlam : 0 < lam) (hτ : 0 < τ)
    (δ : Vec N → Vec N → ℝ) (hδ : IsNormSemimetric δ)
    (X : Set (Vec K)) (g : Vec N → Vec K) (hgX : ∀ z ∈ Z, g z ∈ X) (hg_inj : Set.InjOn g Z)
    (f : Vec K → Vec N) (hf : ∀ x ∈ X, f x ∈ Z')
    (hmeas : AEMeasurable (f ∘ g) (volume.restrict Z)) :
    Tendsto (fun M : ℕ => deltaInfoNCE lam δ τ δ Z (f ∘ g) M - Real.log M) atTop
      (𝓝 (deltaAlign lam δ τ δ Z (f ∘ g) + deltaUnif τ δ Z (f ∘ g))) := by sorry

end ContrastiveInverts
