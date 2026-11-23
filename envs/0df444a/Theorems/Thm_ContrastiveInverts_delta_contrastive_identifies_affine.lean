-- Prove2me | Theorems.Thm_ContrastiveInverts_delta_contrastive_identifies_affine
-- name    : ContrastiveInverts.delta_contrastive_identifies_affine
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:47:21.42975+00:00
-- url     : https://prove2.me/theorems/7a1da982-28d9-495c-8b09-b58afe37270b
-- title:
--   Theorem 5: minimizers of $\mathcal{L}_{\delta\text{-contr}}$ recover the latents on a convex body up to an invertible affine map
-- statement:
--   Let $Z$ be a convex body in $\mathbb{R}^N$, $N\le K$, and $\tau>0$. Let $\delta$ be a metric induced by a norm, or a semi-metric $j\circ\delta'$ of such a metric as in Lemma 1. Let the marginal be uniform and the conditional be as in eq. (5), $p(\tilde z\mid z)=C_p(z)^{-1}e^{-\delta(\tilde z,z)}$. Let the mixing function $g$ be differentiable and injective on $Z$ with $g(Z)\subseteq\mathcal X\subseteq\mathbb{R}^K$.
--
--   Let $\mathcal F$ be a class of encoders $f:\mathcal X\to Z$ with $f\circ g$ measurable on $Z$. Assume the form of $q_h(\tilde z\mid z)=C_q(z)^{-1}e^{-\delta(h(\tilde z),h(z))/\tau}$ matches $p$: some $f_0\in\mathcal F$ has $q_{f_0\circ g}=p$ on $Z\times Z$. If $f\in\mathcal F$ is differentiable on $\mathcal X$ and minimises $\lim_{M\to\infty}(\mathcal{L}_{\delta\text{-contr}}(f;\tau,M)-\log M)$ over $\mathcal F$, then $h=f\circ g$ is invertible and affine: there is an invertible affine map $A$ of $\mathbb{R}^N$ with
--
--   $$f(g(z))=A(z)\qquad\text{for all }z\in Z.$$
--
--   So the latent sources are recovered up to an affine transformation.
--
--   **Formalization Note** "Invertible" is stated as invertibility of the affine map $A$ on $\mathbb{R}^N$. The paper's $h=f\circ g:Z\to Z$ is encoded by encoders with values in $Z$.
-- source:
--   Zimmermann, Sharma, Schneider, Bethge and Brendel, Contrastive Learning Inverts the Data Generating Process, ICML 2021, arXiv:2102.08850v4, Section 3.3, Theorem 5, eqs. (5)-(7), p. 5; restated with proof in Appendix A.2.4, Theorem 5, p. 18; standing assumptions of Appendix A.2.1, p. 15

import Mathlib
import Definitions.Def_ContrastiveInverts_Basic

open MeasureTheory Filter Topology

namespace ContrastiveInverts

theorem delta_contrastive_identifies_affine {N K : ℕ} (hNK : N ≤ K) (Z : Set (Vec N))
    (hZ : IsConvexBody Z) (τ : ℝ) (hτ : 0 < τ)
    (δ : Vec N → Vec N → ℝ) (hδ : IsNormSemimetric δ)
    (X : Set (Vec K)) (g : Vec N → Vec K) (hgX : ∀ z ∈ Z, g z ∈ X) (hg_inj : Set.InjOn g Z)
    (hg_diff : DifferentiableOn ℝ g Z)
    (F : Set (Vec K → Vec N))
    (hF : ∀ f' ∈ F, (∀ x ∈ X, f' x ∈ Z) ∧ AEMeasurable (f' ∘ g) (volume.restrict Z))
    (hflex : ∃ f₀ ∈ F, ∀ z ∈ Z, ∀ z' ∈ Z,
      bodyModelCond τ δ Z (f₀ ∘ g) z z' = expCond 1 δ Z z z')
    (f : Vec K → Vec N) (hfF : f ∈ F) (hf_diff : DifferentiableOn ℝ f X)
    (hmin : ∀ f' ∈ F,
      deltaInfoNCELimit 1 δ τ δ Z (f ∘ g) ≤ deltaInfoNCELimit 1 δ τ δ Z (f' ∘ g)) :
    ∃ A : Vec N ≃ᵃ[ℝ] Vec N, ∀ z ∈ Z, f (g z) = A z := by sorry

end ContrastiveInverts
