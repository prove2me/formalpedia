-- Prove2me | Theorems.Thm_ConsistentSubmodular_high_parameter_strict_relay
-- name    : ConsistentSubmodular.high_parameter_strict_relay
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:24.305797+00:00
-- url     : https://prove2.me/theorems/2fab9479-15c0-492d-a82f-45c2eab8159a
-- title:
--   Strictly safe full forward edge at parameter at least $3/2$ after failed credit
-- statement:
--   Let $d,p,\delta,w,b,q\in\mathbb{R}$ satisfy
--
--   * $0\le d<\tfrac14$, $p\ge0$, and (strong credit) $\tfrac12\le p$ or $d\le p(1-p)$;
--   * $\delta\ge0$, $w\ge0$, $\delta+w\le 1-d$, and $\delta+w>0$;
--   * $b\ge p+d$ and $q\ge\tfrac32$;
--   * (attainment) $q\,(\delta+w)=3w-b-3d$;
--   * (failure) $3(1-4d)<\bigl(2(1-d)-b-w\bigr)\,q$.
--
--   Then for every real $z$,
--   $$\tfrac34\;<\;(1-d)-\delta z-(1-d-\delta-w)\,z(1-z).$$
--
--   Geometrically, the right-hand side is the value along the forward edge from the designated vertex, parametrised by $z$, so the edge stays strictly above level $3/4$. The statement serves the high-parameter relay step of the safe-path (certificate) construction in Appendix B, retaining the original initial target.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/RelayError.lean#L136-L172 (`ConsistentSubmodular.high_parameter_strict_relay`)

import Mathlib

theorem ConsistentSubmodular.high_parameter_strict_relay (d p δ w b q : ℝ)
    (hd : 0 ≤ d) (hd4 : d < 1 / 4) (hp : 0 ≤ p)
    (hcredit : (1 : ℝ) / 2 ≤ p ∨ d ≤ p * (1 - p))
    (hδ : 0 ≤ δ) (hw0 : 0 ≤ w) (hr : δ + w ≤ 1 - d)
    (hden : 0 < δ + w) (hb : p + d ≤ b)
    (hq : (3 : ℝ) / 2 ≤ q)
    (hatt : q * (δ + w) = 3 * w - b - 3 * d)
    (hfail : 3 * (1 - 4 * d) < (2 * (1 - d) - b - w) * q) :
    ∀ z : ℝ, (3 : ℝ) / 4 <
      (1 - d) - δ * z - (1 - d - δ - w) * z * (1 - z) := by sorry
