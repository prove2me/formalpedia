-- Prove2me | Theorems.Thm_Arxiv1510_02920_no_vacuum_both_sides
-- name    : Arxiv1510_02920.no_vacuum_both_sides
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T02:11:51.731113+00:00
-- url     : https://prove2.me/theorems/6061bce1-8f67-45c5-8a76-7c3321b57b7b
-- title:
--   Eqs. (4), (6): monotonicity of $f$ rules out vacuum on both sides
-- statement:
--   Let $c>0$, $\gamma>0$ and let $f:\mathbb{R}\to\mathbb{R}$ be differentiable. Suppose the permittivity (3) with $P$ from (4) has no gain (condition (iii)). Then for every real $\omega\ne0$ it is not the case that $P(x,\omega)\to1$ both as $x\to+\infty$ and as $x\to-\infty$. So the medium cannot approach vacuum on both sides.
--
--   **Formalization Note** Vacuum at an end is expressed as $P\to1$ there, the limit $g_\pm=1$ of the ansatz (2). For $P$ of the form (4) this is equivalent to $f\to0$.
-- source:
--   T. G. Philbin, All-frequency reflectionlessness, arXiv:1510.02920v1 (2015), claim c009; unnumbered main text, paragraph after Figure 1, PDF pp. 4-5

import Mathlib
import Definitions.Def_Arxiv1510_02920_Basic

open Filter Topology Asymptotics

namespace Arxiv1510_02920

theorem no_vacuum_both_sides (c : ℝ) (hc : 0 < c) (γ : ℝ) (hγ : 0 < γ)
    (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hgain : CondNoGain (perm c (ansatzP f γ))) (ω : ℝ) (hω : ω ≠ 0) :
    ¬ (Tendsto (fun x : ℝ => ansatzP f γ x (ω : ℂ)) atTop (𝓝 1) ∧
        Tendsto (fun x : ℝ => ansatzP f γ x (ω : ℂ)) atBot (𝓝 1)) := by sorry

end Arxiv1510_02920
