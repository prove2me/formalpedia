-- Prove2me | Theorems.Thm_ContrastiveInverts_body_ce_minimizers_are_isometries
-- name    : ContrastiveInverts.body_ce_minimizers_are_isometries
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T18:45:57.311816+00:00
-- url     : https://prove2.me/theorems/7e314ab8-9bba-494b-8cd7-06d1fc6ed07d
-- title:
--   Proposition 4 (as proved): continuous minimizers of the cross-entropy are isometries, $\lambda\tau\,\delta(z,\tilde z)=\delta(h(z),h(\tilde z))$
-- statement:
--   Let $Z$ and $Z'$ be convex bodies in $\mathbb{R}^N$, and $\lambda,\tau>0$. Let $\delta$ be a metric induced by a norm, or a semi-metric $j\circ\delta'$ of such a metric. Let $p(\tilde z\mid z)=C_p(z)^{-1}e^{-\lambda\delta(\tilde z,z)}$ and $q_h(\tilde z\mid z)=C_h(z)^{-1}e^{-\delta(h(\tilde z),h(z))/\tau}$, where $C_h(z)=\int_Z e^{-\delta(h(\tilde z),h(z))/\tau}\,d\tilde z$.
--
--   Let $\mathcal H$ be a class of measurable maps $Z\to Z'$ that is flexible enough to match: some $h_0\in\mathcal H$ has $q_{h_0}(\tilde z\mid z)=p(\tilde z\mid z)$ for all $z,\tilde z\in Z$. Let $h\in\mathcal H$ be **continuous on $Z$** and minimise the cross-entropy $\mathbb{E}_{p(\tilde z\mid z)}[-\log q_h(\tilde z\mid z)]$ over $\mathcal H$ at every anchor $z\in Z$. Then
--
--   $$\lambda\tau\,\delta(z,\tilde z)=\delta(h(z),h(\tilde z))\qquad\text{for all }z,\tilde z\in Z.$$
--
--   **Formalization Note** The printed proposition does not assume continuity, and without it the statement is false. Take $N=1$, $Z=[0,1]$, $Z'=[-1,1]$, $\delta(a,b)=|a-b|$ and $\lambda=\tau=1$, and let $h(z)=z$ for $z>0$ and $h(0)=-1$. Then $q_h(\cdot\mid z)=p(\cdot\mid z)$ almost everywhere for every anchor $z$, so $h$ minimises every conditional cross-entropy, yet $\delta(h(0),h(\tilde z))=1+\tilde z\neq\tilde z$. The proof's claim that $q_h$ is continuous needs $h$ continuous, which the paper's Theorems 4–6 supply through differentiability of $f$ and $g$. The displayed conditional in the printed proposition reads $e^{-\delta/\lambda}$, but the printed conclusion $\lambda\tau\,\delta$ and Appendix A.2.1 use $e^{-\lambda\delta}$, which is the form stated here.
-- source:
--   Zimmermann, Sharma, Schneider, Bethge and Brendel, Contrastive Learning Inverts the Data Generating Process, ICML 2021, arXiv:2102.08850v4, Appendix A.2.3, Proposition 4, eqs. (64)-(65) and the display after (65), p. 17; standing assumptions of Appendix A.2.1, p. 15

import Mathlib
import Definitions.Def_ContrastiveInverts_Basic

open MeasureTheory Filter Topology

namespace ContrastiveInverts

theorem body_ce_minimizers_are_isometries {N : ℕ} (Z Z' : Set (Vec N))
    (hZ : IsConvexBody Z) (hZ' : IsConvexBody Z') (lam τ : ℝ) (hlam : 0 < lam) (hτ : 0 < τ)
    (δ : Vec N → Vec N → ℝ) (hδ : IsNormSemimetric δ) (H : Set (Vec N → Vec N))
    (hH : ∀ h' ∈ H, (∀ z ∈ Z, h' z ∈ Z') ∧ AEMeasurable h' (volume.restrict Z))
    (hflex : ∃ h₀ ∈ H, ∀ z ∈ Z, ∀ z' ∈ Z, bodyModelCond τ δ Z h₀ z z' = expCond lam δ Z z z')
    (h : Vec N → Vec N) (hh : h ∈ H) (hcont : ContinuousOn h Z)
    (hmin : ∀ z ∈ Z, ∀ h' ∈ H,
      bodyCondCrossEntropy lam δ τ δ Z h z ≤ bodyCondCrossEntropy lam δ τ δ Z h' z) :
    ∀ z ∈ Z, ∀ z' ∈ Z, lam * τ * δ z z' = δ (h z) (h z') := by sorry

end ContrastiveInverts
