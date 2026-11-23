-- Prove2me | Theorems.Thm_ContrastiveInverts_delta_infonce_limit_cross_entropy
-- name    : ContrastiveInverts.delta_infonce_limit_cross_entropy
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:45:18.663268+00:00
-- url     : https://prove2.me/theorems/662e0290-e071-471a-9715-1e0caf601ab5
-- title:
--   Theorem 3: $\mathcal{L}_{\delta\text{-contr}}$ converges to the cross-entropy between latent distributions on a convex body
-- statement:
--   Let $Z$ and $Z'$ be convex bodies in $\mathbb{R}^N$, $N\le K$, and $\tau,\lambda>0$. Let $\delta$ be a metric induced by a norm, or a semi-metric $j\circ\delta'$ of such a metric. Let the marginal be uniform, $p(z)=|Z|^{-1}$, and the conditional be $p(\tilde z\mid z)=C_p(z)^{-1}e^{-\lambda\delta(\tilde z,z)}$. Consider the model conditional
--
--   $$q_h(\tilde z\mid z)=C_h(z)^{-1}e^{-\delta(h(\tilde z),h(z))/\tau},\qquad C_h(z)=\int_Z e^{-\delta(h(\tilde z),h(z))/\tau}\,d\tilde z,$$
--
--   where $h=f\circ g$, $g$ maps $Z$ injectively into $\mathcal X\subseteq\mathbb{R}^K$, the encoder $f$ maps $\mathcal X$ into $Z'$, and $h$ is measurable on $Z$. Then
--
--   $$\lim_{M\to\infty}\Big(\mathcal{L}_{\delta\text{-contr}}(f;\tau,M)-\log M+\log|Z|\Big)=\mathbb{E}_{z\sim p(z)}\big[H\big(p(\cdot\mid z),q_h(\cdot\mid z)\big)\big],$$
--
--   with $|Z|$ the volume of $Z$.
--
--   **Formalization Note** The model assumption of Appendix A.2.1, $f:\mathcal X\to Z'$ with $Z'$ a convex body, is included; it makes every expectation finite.
-- source:
--   Zimmermann, Sharma, Schneider, Bethge and Brendel, Contrastive Learning Inverts the Data Generating Process, ICML 2021, arXiv:2102.08850v4, Appendix A.2.2, Theorem 3, p. 16; standing assumptions of Appendix A.2.1, p. 15

import Mathlib
import Definitions.Def_ContrastiveInverts_Basic

open MeasureTheory Filter Topology

namespace ContrastiveInverts

theorem delta_infonce_limit_cross_entropy {N K : ℕ} (hNK : N ≤ K) (Z Z' : Set (Vec N))
    (hZ : IsConvexBody Z) (hZ' : IsConvexBody Z') (lam τ : ℝ) (hlam : 0 < lam) (hτ : 0 < τ)
    (δ : Vec N → Vec N → ℝ) (hδ : IsNormSemimetric δ)
    (X : Set (Vec K)) (g : Vec N → Vec K) (hgX : ∀ z ∈ Z, g z ∈ X) (hg_inj : Set.InjOn g Z)
    (f : Vec K → Vec N) (hf : ∀ x ∈ X, f x ∈ Z')
    (hmeas : AEMeasurable (f ∘ g) (volume.restrict Z)) :
    Tendsto (fun M : ℕ => deltaInfoNCE lam δ τ δ Z (f ∘ g) M - Real.log M +
        Real.log (bodyVolume Z)) atTop
      (𝓝 (bodyCrossEntropy lam δ τ δ Z (f ∘ g))) := by sorry

end ContrastiveInverts
