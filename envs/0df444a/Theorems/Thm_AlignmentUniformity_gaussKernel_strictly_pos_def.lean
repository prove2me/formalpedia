-- Prove2me | Theorems.Thm_AlignmentUniformity_gaussKernel_strictly_pos_def
-- name    : AlignmentUniformity.gaussKernel_strictly_pos_def
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:27:16.191465+00:00
-- url     : https://prove2.me/theorems/ed33c8d8-3428-4882-a85c-39879e029cbe
-- title:
--   Lemma 1: strict positive definiteness of $G_t$
-- statement:
--   Let $d\ge0$ and $t>0$. The Gaussian kernel $G_t(u,v)=e^{-t\|u-v\|_2^2}$ is strictly positive definite on $S^d\times S^d$. For every finite signed Borel measure $\mu$ supported on $S^d$,
--
--   $$I_{G_t}[\mu]=\int_{S^d}\int_{S^d}G_t(u,v)\,d\mu(v)\,d\mu(u)\ \ge\ 0,$$
--
--   with equality only if $\mu=0$.
--
--   This is the property of $G_t$ from which the paper derives Propositions 1 and 2.
--
--   **Formalization Note** The signed measure is written as $\mu=\nu_1-\nu_2$ with $\nu_1,\nu_2$ finite Borel measures on $\mathbb{R}^{d+1}$ concentrated on $S^d$. Every finite signed measure has this form. Its energy is expanded as $I(\nu_1,\nu_1)-I(\nu_1,\nu_2)-I(\nu_2,\nu_1)+I(\nu_2,\nu_2)$, and $\mu=0$ becomes $\nu_1=\nu_2$. The paper's definition of strict positive definiteness assumes an infinite set $A$, which excludes $S^0$. The statement is made for every $d\ge0$, including $d=0$, where it also holds.
-- source:
--   Wang and Isola, Understanding Contrastive Representation Learning through Alignment and Uniformity on the Hypersphere, ICML 2020, arXiv:2005.10242v10, Appendix A.1, Lemma 1 and the Definition of strict positive definiteness, p. 14

import Mathlib
import Definitions.Def_AlignmentUniformity_Basic

open MeasureTheory Filter Topology

namespace AlignmentUniformity

theorem gaussKernel_strictly_pos_def (d : ℕ) {t : ℝ} (ht : 0 < t)
    (ν₁ ν₂ : Measure (Vec (d + 1))) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    (h₁ : ν₁ (Metric.sphere (0 : Vec (d + 1)) 1)ᶜ = 0)
    (h₂ : ν₂ (Metric.sphere (0 : Vec (d + 1)) 1)ᶜ = 0) :
    0 ≤ signedEnergy (gaussKernel t) ν₁ ν₂ ∧
      (signedEnergy (gaussKernel t) ν₁ ν₂ = 0 → ν₁ = ν₂) := by sorry

end AlignmentUniformity
