-- Prove2me | Theorems.Thm_ContrastiveInverts_ce_minimizers_preserve_dot_product
-- name    : ContrastiveInverts.ce_minimizers_preserve_dot_product
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:42:21.834402+00:00
-- url     : https://prove2.me/theorems/904b8661-30d7-4509-891c-94ce4a304ecd
-- title:
--   Proposition 1 (as proved): minimizers of the cross-entropy maintain the dot product, $h(z)^\top h(\tilde z)=\tau\kappa\, z^\top\tilde z$
-- statement:
--   Let $N\ge1$, $Z=\mathbb{S}^{N-1}$, $\tau>0$, $\kappa>0$, and let $p(\tilde z\mid z)=C_p^{-1}e^{\kappa z^\top\tilde z}$. Let $\mathcal H$ be a class of measurable maps $h$ sending $Z$ into the sphere of radius $\sqrt{\tau\kappa}$. Suppose the class is flexible enough to match the ground truth: some $h_0\in\mathcal H$ has $q_{h_0}(\tilde z\mid z)=p(\tilde z\mid z)$ for all $z,\tilde z\in Z$. If $h\in\mathcal H$ minimises the cross-entropy $\mathbb{E}_{p(\tilde z\mid z)}[-\log q_h(\tilde z\mid z)]$ over $\mathcal H$ at every anchor $z\in Z$, then for all $z,\tilde z\in Z$
--
--   $$p(\tilde z\mid z)=q_h(\tilde z\mid z)\qquad\text{and}\qquad \tau\kappa\,z^\top\tilde z=h(z)^\top h(\tilde z).$$
--
--   **Formalization Note** The paper prints the second conclusion as $\kappa z^\top\tilde z=h(z)^\top h(\tilde z)$. Its proof, which omits the factor $1/\tau$ in the last step, actually yields $\tau\kappa\,z^\top\tilde z=h(z)^\top h(\tilde z)$, and that is what is stated. The printed form fails for the matching map $h(z)=\sqrt{\tau\kappa}\,z$ whenever $\tau\ne1$. "Minimiser of the cross-entropy" is read at each anchor $z$, as printed. Membership of $h_0$ in the class encodes "sufficiently flexible such that $p$ and $q_h$ can match".
-- source:
--   Zimmermann, Sharma, Schneider, Bethge and Brendel, Contrastive Learning Inverts the Data Generating Process, ICML 2021, arXiv:2102.08850v4, Section 3.1, Proposition 1, p. 4; restated with proof in Appendix A.1.2, Proposition 1, eqs. (32)-(36), p. 14

import Mathlib
import Definitions.Def_ContrastiveInverts_Basic

open MeasureTheory Filter Topology

namespace ContrastiveInverts

theorem ce_minimizers_preserve_dot_product {N : ℕ} (hN : 0 < N) (τ κ : ℝ) (hτ : 0 < τ)
    (hκ : 0 < κ) (H : Set (Vec N → Vec N))
    (hH : ∀ h' ∈ H, (∀ z ∈ Metric.sphere (0 : Vec N) 1,
        h' z ∈ Metric.sphere (0 : Vec N) (Real.sqrt (τ * κ))) ∧
      Measurable (fun z : Sph N => h' z))
    (hflex : ∃ h₀ ∈ H, ∀ z ∈ Metric.sphere (0 : Vec N) 1, ∀ z' ∈ Metric.sphere (0 : Vec N) 1,
      sphModelCond τ h₀ z z' = vmfCond N κ z z')
    (h : Vec N → Vec N) (hh : h ∈ H)
    (hmin : ∀ z ∈ Metric.sphere (0 : Vec N) 1, ∀ h' ∈ H,
      sphCondCrossEntropy κ τ h z ≤ sphCondCrossEntropy κ τ h' z) :
    (∀ z ∈ Metric.sphere (0 : Vec N) 1, ∀ z' ∈ Metric.sphere (0 : Vec N) 1,
      vmfCond N κ z z' = sphModelCond τ h z z') ∧
    (∀ z ∈ Metric.sphere (0 : Vec N) 1, ∀ z' ∈ Metric.sphere (0 : Vec N) 1,
      τ * κ * inner ℝ z z' = inner ℝ (h z) (h z')) := by sorry

end ContrastiveInverts
