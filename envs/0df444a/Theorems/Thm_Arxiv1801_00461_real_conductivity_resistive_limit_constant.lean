-- Prove2me | Theorems.Thm_Arxiv1801_00461_real_conductivity_resistive_limit_constant
-- name    : Arxiv1801_00461.real_conductivity_resistive_limit_constant
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:14:13.909049+00:00
-- url     : https://prove2.me/theorems/15c56207-9189-4c53-83e4-2285afd95d4f
-- title:
--   Eq. (37): a real conductivity with a resistive high-frequency limit is constant
-- statement:
--   Let $k\in\mathbb R$ and let the conductivity of a medium with resistive high-frequency limit $k$ be $\sigma_e(\omega)=k+\int_0^\infty d(\tau)e^{-i\omega\tau}d\tau$, where the deviation kernel $d$ is real and integrable on $(0,\infty)$.
--
--   1. If $\operatorname{Im}\sigma_e(\omega)=0$ for every real $\omega$, then $\sigma_e(\omega)=k$ for every $\omega$ (eq. (37)). A real, frequency-dependent conductivity with a real constant limit is incompatible with causality.
--   2. In particular, for any real $x$ and $c\ne0$ no such $\sigma_e$ satisfies $\sigma_e(\omega)=\omega^xe^{-\omega/c}+k$ for all $\omega>0$.
--
--   **Formalization Note** The limit $\lim_{\omega\to\infty}\sigma_e=k$ is encoded by taking the asymptote $\sigma_\infty(\omega)$ equal to the constant $k$, the transform of $k\,\delta(t)$. The remark that the conductivity need not be real at large frequencies cites earlier work and is not included.
-- source:
--   Bédard and Destexhe, Kramers-Kronig relations and the properties of conductivity and permittivity in heterogeneous media, arXiv:1801.00461v1 (2018), claim c013; Sec. 3.1.1, eq. (37) and the following three paragraphs, PDF p. 12

import Mathlib
import Definitions.Def_Arxiv1801_00461_Basic

open MeasureTheory Filter Topology

namespace Arxiv1801_00461

theorem real_conductivity_resistive_limit_constant (k : ℝ) :
    (∀ dsig : ℝ → ℝ, IntegrableOn dsig (Set.Ioi 0) →
      (∀ ω : ℝ, (condFreq (fun _ => (k : ℂ)) dsig ω).im = 0) → ∀ ω : ℝ, condFreq (fun _ => (k : ℂ)) dsig ω = k) ∧
    (∀ x c : ℝ, c ≠ 0 → ¬ ∃ dsig : ℝ → ℝ, IntegrableOn dsig (Set.Ioi 0) ∧
      ∀ ω : ℝ, 0 < ω → condFreq (fun _ => (k : ℂ)) dsig ω = ((ω ^ x * Real.exp (-ω / c) + k : ℝ) : ℂ)) := by sorry

end Arxiv1801_00461
