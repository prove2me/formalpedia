-- Prove2me | Theorems.Thm_ContrastiveInverts_delta_contrastive_identifies_permutation
-- name    : ContrastiveInverts.delta_contrastive_identifies_permutation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:48:00.348836+00:00
-- url     : https://prove2.me/theorems/09eca6c0-626e-4ddf-85fb-dc7a8a44ca08
-- title:
--   Theorem 6 (as proved): for $L^\alpha$ similarities, $\alpha\ne2$, minimizers recover the latents up to permutation, sign flips, rescaling and a translation
-- statement:
--   Let $Z$ be a convex body in $\mathbb{R}^N$, $N\le K$, $\alpha\ge1$ with $\alpha\ne2$, and $\tau>0$. Let $\delta=j\circ d_\alpha$, where $d_\alpha(a,b)=(\sum_i|a_i-b_i|^\alpha)^{1/\alpha}$ is the $L^\alpha$ metric and $j$ is a continuous bijection of $[0,\infty)$ with $j(0)=0$. This includes $d_\alpha$ itself and its $\alpha$-th power. Let the marginal be uniform and $p(\tilde z\mid z)=C_p(z)^{-1}e^{-\delta(\tilde z,z)}$ (eq. 5). Let $g$ be differentiable and injective on $Z$ with $g(Z)\subseteq\mathcal X\subseteq\mathbb{R}^K$.
--
--   Let the model use the same metric up to a constant factor $s>0$, so that $q_h(\tilde z\mid z)=C_q(z)^{-1}e^{-s\,\delta(h(\tilde z),h(z))/\tau}$ and the objective is $\mathcal{L}_{\delta\text{-contr}}$ with similarity $s\,\delta$. Let $\mathcal F$ be a class of encoders $f:\mathcal X\to Z$ with $f\circ g$ measurable on $Z$, containing some $f_0$ with $q_{f_0\circ g}=p$ on $Z\times Z$. If $f\in\mathcal F$ is differentiable on $\mathcal X$ and minimises this objective for $M\to\infty$ over $\mathcal F$, then there are a permutation $\sigma$ of $\{1,\dots,N\}$, signs $\varepsilon_i\in\{\pm1\}$, a factor $c>0$ and a vector $b\in\mathbb{R}^N$ with
--
--   $$f(g(z))_i=c\,\varepsilon_i\,z_{\sigma(i)}+b_i\qquad\text{for all }z\in Z,\ i=1,\dots,N.$$
--
--   So $h$ is a composition of a permutation, sign flips, a rescaling and a translation.
--
--   **Formalization Note** The paper's conclusion omits the translation $b$, and without it the statement is false. On $Z=[0,1]^N$ with $\tau=s=1$, the map $h(z)=\mathbf 1-z$ sends $Z$ onto $Z$ and preserves every $L^\alpha$ distance. It therefore has exactly the loss of the identity and is a minimiser, but $h(0)\neq0$. The proof establishes the statement with $b$: Theorem 5 makes $h$ affine, and only its linear part is a scaled generalized permutation. The class of $\delta$ follows the main-text statement (an $L^\alpha$ metric or a semi-metric of it in the sense of Lemma 1); the appendix restatement names the $L^\alpha$ metric and its $\alpha$-th power, both of which are covered.
-- source:
--   Zimmermann, Sharma, Schneider, Bethge and Brendel, Contrastive Learning Inverts the Data Generating Process, ICML 2021, arXiv:2102.08850v4, Section 3.3, Theorem 6, eqs. (5)-(6), p. 5; restated with proof in Appendix A.2.4, Theorem 6, eqs. (74)-(75), p. 18; standing assumptions of Appendix A.2.1, p. 15

import Mathlib
import Definitions.Def_ContrastiveInverts_Basic

open MeasureTheory Filter Topology

namespace ContrastiveInverts

theorem delta_contrastive_identifies_permutation {N K : ℕ} (hNK : N ≤ K) (Z : Set (Vec N))
    (hZ : IsConvexBody Z) (α : ℝ) (hα : 1 ≤ α) (hα2 : α ≠ 2)
    (δ : Vec N → Vec N → ℝ) (hδ : ∃ j : ℝ → ℝ, IsReparam j ∧ ∀ a b, δ a b = j (lpDist α a b))
    (s τ : ℝ) (hs : 0 < s) (hτ : 0 < τ)
    (X : Set (Vec K)) (g : Vec N → Vec K) (hgX : ∀ z ∈ Z, g z ∈ X) (hg_inj : Set.InjOn g Z)
    (hg_diff : DifferentiableOn ℝ g Z)
    (F : Set (Vec K → Vec N))
    (hF : ∀ f' ∈ F, (∀ x ∈ X, f' x ∈ Z) ∧ AEMeasurable (f' ∘ g) (volume.restrict Z))
    (hflex : ∃ f₀ ∈ F, ∀ z ∈ Z, ∀ z' ∈ Z,
      bodyModelCond τ (fun a b => s * δ a b) Z (f₀ ∘ g) z z' = expCond 1 δ Z z z')
    (f : Vec K → Vec N) (hfF : f ∈ F) (hf_diff : DifferentiableOn ℝ f X)
    (hmin : ∀ f' ∈ F,
      deltaInfoNCELimit 1 δ τ (fun a b => s * δ a b) Z (f ∘ g) ≤
        deltaInfoNCELimit 1 δ τ (fun a b => s * δ a b) Z (f' ∘ g)) :
    ∃ (σ : Equiv.Perm (Fin N)) (ε : Fin N → ℝ) (c : ℝ) (b : Vec N),
      (∀ i, ε i = 1 ∨ ε i = -1) ∧ 0 < c ∧
        ∀ z ∈ Z, ∀ i, f (g z) i = c * ε i * z (σ i) + b i := by sorry

end ContrastiveInverts
