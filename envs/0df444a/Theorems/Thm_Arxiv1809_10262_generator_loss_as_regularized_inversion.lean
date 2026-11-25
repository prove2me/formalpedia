-- Prove2me | Theorems.Thm_Arxiv1809_10262_generator_loss_as_regularized_inversion
-- name    : Arxiv1809_10262.generator_loss_as_regularized_inversion
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T14:20:26.489411+00:00
-- url     : https://prove2.me/theorems/d90b7b71-03dc-4362-929b-53d3fec67427
-- title:
--   Eq. (9) (as proved): the generator loss (8) is a regularized-inversion objective
-- statement:
--   Let velocity maps have width $w\ge1$ and height $h\ge1$. Let $(m_k,d_k)$, $k=1,\dots,N$ with $N\ge1$, be training pairs of velocity maps and seismic data. Let the seismic data have a probability distribution $\mu$, let $D$ be a real function on velocity maps (the discriminator), and let $\lambda_1,\lambda_2>0$. Let $\mathcal G$ be a class of measurable generators $g$ such that $D$ is integrable under $\mathbb{P}_g=g_\#\mu$ for every $g\in\mathcal G$.
--
--   Then for every $g\in\mathcal G$ the mean over the training pairs of the generator loss (8) equals the regularized-inversion objective (9) with weights $\lambda_1/(Nwh)$ and $\lambda_2/(Nwh)$:
--   $$\frac1N\sum_{k=1}^N L_g(m_k,d_k)=\frac{\lambda_1}{Nwh}\sum_{k=1}^{N}\|m_k-g(d_k)\|_1+\frac{\lambda_2}{Nwh}\sum_{k=1}^{N}\|m_k-g(d_k)\|_2^2-\mathbb{E}_{\tilde x\sim\mathbb{P}_g}D(\tilde x).$$
--   Consequently the minimisers over $\mathcal G$ of the two objectives coincide:
--   $$\operatorname*{argmin}_{g\in\mathcal G}\frac1N\sum_{k=1}^N L_g(m_k,d_k)=\operatorname*{argmin}_{g\in\mathcal G}J_{\lambda_1/(Nwh),\,\lambda_2/(Nwh)}(g).$$
--
--   **Formalization Note** The paper says that eq. (8) "can be rewritten" as eq. (9) with the same symbols $\lambda_1,\lambda_2$. That is not an identity. Eq. (8) is normalised by $1/(wh)$ and is written for one map, while eq. (9) sums over the $N$ pairs without normalisation, and the adversarial term is not summed in either. With the same $\lambda_1,\lambda_2$ the two minimisers differ in general: for $N=2$, $w=h=1$, $\lambda_1=50$, $\lambda_2=100$, constant generators $g\equiv c$, $m_1=m_2=0$ and $D(x)=100x$, the mean of (8) is minimised at $c=1/4$ and (9) at $c=0$. The statement therefore records what the rewriting establishes: equality after rescaling the content weights by $1/(Nwh)$, the reading the paper's word "rewrite" permits. The interpretation of $-\mathbb{E}D$ as a regulariser learned from data is an analogy and is not formalised. The measurability and integrability hypotheses only make the expectation in (8) and (9) well defined. The hypothesis $N\ge1$ is necessary: for $N=0$ the mean is $0$ while the right side is $-\mathbb{E}D$. The positivity of $w,h,\lambda_1,\lambda_2$ is the paper's setting ($\lambda_1=50$, $\lambda_2=100$; the maps are $150\times100$ in the dataset description and $100\times100$ at the generator output) and is not needed for truth.
-- source:
--   Z. Zhang and Y. Lin, Data-driven Seismic Waveform Inversion: A Study on the Robustness and Generalization, arXiv:1809.10262v8 (2018), claim c003; Section III-D (Connection to Regularization Theory), eq. (9) rewriting eq. (8) of Section III-C, PDF p. 5

import Mathlib
import Definitions.Def_Arxiv1809_10262_Basic

open MeasureTheory

namespace Arxiv1809_10262

theorem generator_loss_as_regularized_inversion {Dat : Type*} [MeasurableSpace Dat]
    {w h N : ℕ} (hw : 0 < w) (hh : 0 < h) (hN : 0 < N)
    (lam1 lam2 : ℝ) (hlam1 : 0 < lam1) (hlam2 : 0 < lam2)
    (μ : Measure Dat) [IsProbabilityMeasure μ] (D : VelocityMap w h → ℝ)
    (m : Fin N → VelocityMap w h) (d : Fin N → Dat)
    (G : Set (Dat → VelocityMap w h))
    (hG : ∀ g ∈ G, Measurable g ∧ Integrable D (generatedLaw μ g)) :
    (∀ g ∈ G, meanGeneratorLoss lam1 lam2 μ D m d g =
      regularizedInversionObjective (lam1 / ((N : ℝ) * w * h)) (lam2 / ((N : ℝ) * w * h))
        μ D m d g) ∧
    {g | g ∈ G ∧ IsMinOn (meanGeneratorLoss lam1 lam2 μ D m d) G g} =
      {g | g ∈ G ∧ IsMinOn (regularizedInversionObjective (lam1 / ((N : ℝ) * w * h))
        (lam2 / ((N : ℝ) * w * h)) μ D m d) G g} := by sorry

end Arxiv1809_10262
