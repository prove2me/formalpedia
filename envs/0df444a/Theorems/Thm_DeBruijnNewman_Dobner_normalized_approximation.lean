-- Prove2me | Theorems.Thm_DeBruijnNewman_Dobner_normalized_approximation
-- name    : DeBruijnNewman.Dobner.normalized_approximation
-- status  : Proved
-- author  : @adobner
-- created : 2026-09-24T21:41:14.23579+00:00
-- url     : https://prove2.me/theorems/31c2b281-f89c-4a54-a0ef-72fec818ac2f
-- title:
--   Dobner's Theorem 4: uniform approximation on each fixed vertical strip
-- statement:
--   Fix $t<0$. With the explicit functions
--
--   $$
--   J_t(s)=s+\frac{|t|}{4}\Log\!\left(\frac{s}{2\pi}\right),\quad
--   \gamma_t(s)=\gamma(s)\exp\!\left(\frac{(s-J_t(s))^2}{|t|}\right),\quad
--   h_t(s)=\frac{8H_t(-i(2J_t(s)-1))}{\gamma_t(s)},
--   $$
--
--   where
--
--   $$
--   \gamma(s)=\frac{s(s-1)}2\pi^{-s/2}\Gamma(s/2),
--   $$
--
--   the function $h_t$ is holomorphic in the upper half-plane. Moreover, for every real pair $a<b$ and every $\varepsilon>0$, there exists $Y\in\mathbb R$ such that
--
--   $$
--   |h_t(s)-Z_t(s)|<\varepsilon
--   $$
--
--   whenever
--
--   $$
--   a\leq\operatorname{Re}s\leq b,\qquad
--   Y\leq\operatorname{Im}s.
--   $$
--
--   Here $Z_t(s)=\sum_{n\geq1}\exp(\frac{t}{4}\log^2n)n^{-s}$. This is the fixed-time, fixed-strip qualitative consequence of Dobner's asymptotic formula, together with the holomorphy used in Section 3.1. The height threshold may depend on $t,a,b,\varepsilon$; no uniformity as $t$ approaches zero is asserted.
--
--   **Formalization Note** Holomorphy is expressed as complex differentiability on the open upper half-plane. The heat flow is the canonical platform integral from `DeBruijnNewman_core`, with the factor-eight normalization made explicit.
-- source:
--   Alexander Dobner, A proof of Newman's conjecture for the extended Selberg class, arXiv:2005.05142v2 (10 January 2026), https://arxiv.org/abs/2005.05142v2, Theorem 4, equation (10) and definitions (11)–(13), pp. 12–13; its qualitative fixed-strip consequence (14), p. 13, and the holomorphy assertion and equations (15)–(16) in Section 3.1, pp. 14–15. Specialized to F = zeta with the factor-eight normalization of the canonical H.

import Definitions.Def_DeBruijnNewman_Dobner
open Metric

theorem DeBruijnNewman.Dobner.normalized_approximation (t : ℝ) (ht : t < 0) :
    DifferentiableOn ℂ (DeBruijnNewman.Dobner.normalizedXi t) {s : ℂ | 0 < s.im} ∧
      ∀ (a b : ℝ), a < b → ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ,
        ∀ s : ℂ, a ≤ s.re → s.re ≤ b → Y ≤ s.im →
          ‖DeBruijnNewman.Dobner.normalizedXi t s
            - DeBruijnNewman.Dobner.zetaT t s‖ < ε := by sorry
