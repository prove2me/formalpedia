-- Prove2me | Theorems.Thm_ContrastiveInverts_body_ce_minimizers_affine
-- name    : ContrastiveInverts.body_ce_minimizers_affine
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:46:40.707137+00:00
-- url     : https://prove2.me/theorems/da776188-4816-44ce-9cc3-acfb952a29fa
-- title:
--   Theorem 4: minimizers of the cross-entropy on a convex body are affine
-- statement:
--   Let $Z=Z'$ be a convex body in $\mathbb{R}^N$, $N\le K$, and $\lambda,\tau>0$. Let $\delta$ be a metric induced by a norm, or a semi-metric $j\circ\delta'$ of such a metric. Let $p(\tilde z\mid z)=C_p(z)^{-1}e^{-\lambda\delta(\tilde z,z)}$ with uniform marginal on $Z$. Let the mixing function $g$ be differentiable and injective on $Z$ with $g(Z)\subseteq\mathcal X\subseteq\mathbb{R}^K$.
--
--   Let $\mathcal F$ be a class of encoders $f:\mathcal X\to Z$ with $f\circ g$ measurable on $Z$. Assume the class can match $p$: some $f_0\in\mathcal F$ has $q_{f_0\circ g}(\tilde z\mid z)=p(\tilde z\mid z)$ for all $z,\tilde z\in Z$, with $q_h$ as in eq. (7). If $f\in\mathcal F$ is differentiable on $\mathcal X$ and minimises $\mathbb{E}_{z\sim p(z)}H(p(\cdot\mid z),q_{f\circ g}(\cdot\mid z))$ over $\mathcal F$, then $h=f\circ g$ is affine on $Z$: there is an affine map $A$ of $\mathbb{R}^N$ with $f(g(z))=A(z)$ for all $z\in Z$.
--
--   **Formalization Note** "Minimises the cross-entropy between $p$ and $q_h$" is read as minimising the expected cross-entropy, the quantity that Theorem 3 relates to $\mathcal{L}_{\delta\text{-contr}}$.
-- source:
--   Zimmermann, Sharma, Schneider, Bethge and Brendel, Contrastive Learning Inverts the Data Generating Process, ICML 2021, arXiv:2102.08850v4, Appendix A.2.4, Theorem 4, p. 18; standing assumptions of Appendix A.2.1, p. 15

import Mathlib
import Definitions.Def_ContrastiveInverts_Basic

open MeasureTheory Filter Topology

namespace ContrastiveInverts

theorem body_ce_minimizers_affine {N K : ℕ} (hNK : N ≤ K) (Z : Set (Vec N))
    (hZ : IsConvexBody Z) (lam τ : ℝ) (hlam : 0 < lam) (hτ : 0 < τ)
    (δ : Vec N → Vec N → ℝ) (hδ : IsNormSemimetric δ)
    (X : Set (Vec K)) (g : Vec N → Vec K) (hgX : ∀ z ∈ Z, g z ∈ X) (hg_inj : Set.InjOn g Z)
    (hg_diff : DifferentiableOn ℝ g Z)
    (F : Set (Vec K → Vec N))
    (hF : ∀ f' ∈ F, (∀ x ∈ X, f' x ∈ Z) ∧ AEMeasurable (f' ∘ g) (volume.restrict Z))
    (hflex : ∃ f₀ ∈ F, ∀ z ∈ Z, ∀ z' ∈ Z,
      bodyModelCond τ δ Z (f₀ ∘ g) z z' = expCond lam δ Z z z')
    (f : Vec K → Vec N) (hfF : f ∈ F) (hf_diff : DifferentiableOn ℝ f X)
    (hmin : ∀ f' ∈ F,
      bodyCrossEntropy lam δ τ δ Z (f ∘ g) ≤ bodyCrossEntropy lam δ τ δ Z (f' ∘ g)) :
    ∃ A : Vec N →ᵃ[ℝ] Vec N, ∀ z ∈ Z, f (g z) = A z := by sorry

end ContrastiveInverts
