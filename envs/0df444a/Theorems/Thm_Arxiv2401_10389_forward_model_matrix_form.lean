-- Prove2me | Theorems.Thm_Arxiv2401_10389_forward_model_matrix_form
-- name    : Arxiv2401_10389.forward_model_matrix_form
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:13:56.023015+00:00
-- url     : https://prove2.me/theorems/1e676c28-cd28-4052-80d1-e16ccb06bd2e
-- title:
--   Eq. (6): the aberrated forward model is $\hat M(\Gamma,u)=u\circ Hu$
-- statement:
--   Let a probe with $N_e$ elements insonify $N_s$ point scatterers, with transmission and reflection operators $T,R\in\mathbb{C}^{N_e\times N_s}$ and diagonal backscattering matrix $\Gamma=\operatorname{diag}(\gamma)$. For every aberration vector $u\in\mathbb{C}^{N_e}$ acting identically on transmit and receive, the model signal of eq. (5) is given by the matrix form
--
--   $$\hat M(\Gamma,u)=u\circ Hu,\qquad H=R\,\Gamma\,T^T,$$
--
--   that is, $\sum_{s}\sum_{n}u_mR_{m,s}\Gamma_{s,s}T_{n,s}u_n=u_m(Hu)_m$ for every element $m$.
--
--   The transfer matrix $H$ contains all of the wave propagation and does not depend on the aberration, which enters only through $u$.
--
--   **Formalization Note** The identity is stated for arbitrary complex matrices $R$, $T$ and vectors $\gamma$, $u$. The paper builds $T$ and $R$ from Green's functions (Supplemental materials A, B) but uses none of that structure here.
-- source:
--   Xing, Malescot, Martineau, Rungta and Provost, Inverse Problem Approach to Aberration Correction for in vivo Transcranial Imaging Based on a Sparse Representation of Contrast-enhanced Ultrasound Data, arXiv:2401.10389v3 (2025), claim c025; Section II.A eq. (5) and Section II.B eqs. (6), (7), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv2401_10389_Basic

open Matrix Filter Topology Asymptotics

namespace Arxiv2401_10389

theorem forward_model_matrix_form {Ne Ns : ℕ} (R : Matrix (Fin Ne) (Fin Ns) ℂ) (γ : Fin Ns → ℂ)
    (T : Matrix (Fin Ne) (Fin Ns) ℂ) (u : Fin Ne → ℂ) :
    aberratedSignal R γ T u = forwardModel R γ T u := by sorry

end Arxiv2401_10389
