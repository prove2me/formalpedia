-- Prove2me | Theorems.Thm_ConsistentSubmodular_high_anchor_gap
-- name    : ConsistentSubmodular.high_anchor_gap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:22.716475+00:00
-- url     : https://prove2.me/theorems/07466dcc-1fb4-43a9-b4cb-93e24c23fd72
-- title:
--   High anchors: failed credit forces a residual gap beyond $3d$
-- statement:
--   Let $d,p,\delta,w,b,q\in\mathbb{R}$ with
--
--   * $0<d\le\tfrac{7}{40}$ and $p\ge 0$;
--   * (strong credit) $\tfrac12\le p$ or $d\le p(1-p)$;
--   * $\delta\ge0$, $b\ge p+d$, and $1\le q<3$;
--   * (attainment) $q(\delta+w)=3w-b-3d$;
--   * (failure) $3(1-4d)<\bigl(2(1-d)-b-w\bigr)\,q$.
--
--   Then
--   $$3d\;<\;w .$$
--
--   In words, when the credit test fails at a high anchor, the attaining residual gap $w$ exceeds the deficit budget $3d$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/HighAnchor.lean#L105-L192 (`ConsistentSubmodular.high_anchor_gap`)

import Mathlib

theorem ConsistentSubmodular.high_anchor_gap (d p δ w b q : ℝ)
    (hd : 0 < d) (hd7 : d ≤ 7 / 40) (hp : 0 ≤ p)
    (hcredit : (1 : ℝ) / 2 ≤ p ∨ d ≤ p * (1 - p))
    (hδ : 0 ≤ δ) (hb : p + d ≤ b) (hq1 : 1 ≤ q) (hq3 : q < 3)
    (hatt : q * (δ + w) = 3 * w - b - 3 * d)
    (hfail : 3 * (1 - 4 * d) < (2 * (1 - d) - b - w) * q) :
    3 * d < w := by sorry
