-- Prove2me | Theorems.Thm_ContrastiveInverts_contrastive_learning_inverts_on_sphere
-- name    : ContrastiveInverts.contrastive_learning_inverts_on_sphere
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:44:08.156505+00:00
-- url     : https://prove2.me/theorems/1c627d8b-30f9-483c-a3d4-82f53f95d686
-- title:
--   Theorem 2: minimizers of the InfoNCE loss invert the generative process on the hypersphere up to an orthogonal transformation and scaling
-- statement:
--   Let $N\ge1$, $N\le K$, $\tau>0$ and $\kappa>0$. Let the latents lie on $Z=\mathbb{S}^{N-1}$ with uniform marginal and von Mises–Fisher conditional $p(\tilde z\mid z)=C_p^{-1}e^{\kappa z^\top\tilde z}$. Let the mixing function $g$ map $Z$ injectively into $\mathcal{X}\subseteq\mathbb{R}^K$ and be differentiable on an open neighbourhood of $Z$.
--
--   Let $\mathcal F$ be a class of encoders $f:\mathcal{X}\to\mathbb{S}^{N-1}_{\sqrt{\tau\kappa}}$, each with $f\circ g$ measurable on $Z$. Assume the model's form of $q_h$ matches $p$: some $f_0\in\mathcal F$ has $q_{f_0\circ g}=p$ on $Z\times Z$. Let $f\in\mathcal F$ be differentiable on $\mathcal X$, with $h=f\circ g$ differentiable on an open neighbourhood of $Z$, and let $f$ minimise the contrastive loss for $M\to\infty$ over $\mathcal F$:
--
--   $$\lim_{M\to\infty}\big(\mathcal{L}_{\mathsf{contr}}(f;\tau,M)-\log M\big)\le\lim_{M\to\infty}\big(\mathcal{L}_{\mathsf{contr}}(f';\tau,M)-\log M\big)\quad\text{for all }f'\in\mathcal F.$$
--
--   Then $h$ is linear on $Z$: there is an orthogonal map $U$ of $\mathbb{R}^N$ with
--
--   $$f(g(z))=\sqrt{\tau\kappa}\;Uz\qquad\text{for all }z\in Z.$$
--
--   So $f$ recovers the latent sources up to an orthogonal linear transformation and the constant scaling factor $\sqrt{\tau\kappa}$.
--
--   **Formalization Note** "The assumed form of $q_h$ matches that of $p$" is encoded as in Proposition 1: the encoders map into the sphere of radius $\sqrt{\tau\kappa}$, and the class contains an encoder whose $q_h$ equals $p$. Minimisation is over this class, whose members are required to give measurable $h$, so that every objective in the comparison is defined. Following Section 3, $g$ is only required to map $Z$ into $\mathcal X$.
-- source:
--   Zimmermann, Sharma, Schneider, Bethge and Brendel, Contrastive Learning Inverts the Data Generating Process, ICML 2021, arXiv:2102.08850v4, Section 3.2, Theorem 2, p. 4; restated with proof in Appendix A.1.2, Theorem 2, p. 15; standing assumptions of Appendix A.1.1, p. 13

import Mathlib
import Definitions.Def_ContrastiveInverts_Basic

open MeasureTheory Filter Topology

namespace ContrastiveInverts

theorem contrastive_learning_inverts_on_sphere {N K : ℕ} (hN : 0 < N) (hNK : N ≤ K)
    (τ κ : ℝ) (hτ : 0 < τ) (hκ : 0 < κ)
    (X : Set (Vec K)) (g : Vec N → Vec K) (hgX : ∀ z ∈ Metric.sphere (0 : Vec N) 1, g z ∈ X)
    (hg_inj : Set.InjOn g (Metric.sphere (0 : Vec N) 1))
    (hg_diff : ∃ U : Set (Vec N), IsOpen U ∧ Metric.sphere (0 : Vec N) 1 ⊆ U ∧
      DifferentiableOn ℝ g U)
    (F : Set (Vec K → Vec N))
    (hF : ∀ f' ∈ F, (∀ x ∈ X, f' x ∈ Metric.sphere (0 : Vec N) (Real.sqrt (τ * κ))) ∧
      Measurable (fun z : Sph N => f' (g z)))
    (hflex : ∃ f₀ ∈ F, ∀ z ∈ Metric.sphere (0 : Vec N) 1, ∀ z' ∈ Metric.sphere (0 : Vec N) 1,
      sphModelCond τ (f₀ ∘ g) z z' = vmfCond N κ z z')
    (f : Vec K → Vec N) (hfF : f ∈ F) (hf_diff : DifferentiableOn ℝ f X)
    (hh_diff : ∃ U : Set (Vec N), IsOpen U ∧ Metric.sphere (0 : Vec N) 1 ⊆ U ∧
      DifferentiableOn ℝ (f ∘ g) U)
    (hmin : ∀ f' ∈ F, infoNCELimit κ τ (f ∘ g) ≤ infoNCELimit κ τ (f' ∘ g)) :
    ∃ U : Vec N ≃ₗᵢ[ℝ] Vec N, ∀ z ∈ Metric.sphere (0 : Vec N) 1,
      f (g z) = Real.sqrt (τ * κ) • U z := by sorry

end ContrastiveInverts
