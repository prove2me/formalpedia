-- Prove2me | Theorems.Thm_ConsistentSubmodular_high_anchor_strict_relay
-- name    : ConsistentSubmodular.high_anchor_strict_relay
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:24.999807+00:00
-- url     : https://prove2.me/theorems/c27b415e-82ea-4a38-8b32-90ca703bd86c
-- title:
--   High anchors: strictly safe forward edge after failed credit
-- statement:
--   Let $d,p,\delta,w,b,q\in\mathbb{R}$ with
--
--   * $0<d\le\tfrac{7}{40}$ and $p\ge0$;
--   * (strong credit) $\tfrac12\le p$ or $d\le p(1-p)$;
--   * $\delta\ge 0$, $\delta+w\le 1-d$, $\delta+w>0$, $b\ge p+d$, and $q\ge 1$;
--   * (attainment) $q(\delta+w)=3w-b-3d$;
--   * (failure) $3(1-4d)<\bigl(2(1-d)-b-w\bigr)\,q$.
--
--   Then for every real $z$,
--   $$\tfrac34\;<\;(1-d)-\delta z-(1-d-\delta-w)\,z(1-z).$$
--
--   This is the high-anchor analogue of the strict relay lemma for parameters $q\ge 3/2$: the forward edge from the designated vertex stays strictly above level $3/4$, which is what the safe-path certificate needs after a failed credit test.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/HighAnchor.lean#L194-L242 (`ConsistentSubmodular.high_anchor_strict_relay`)

import Mathlib

theorem ConsistentSubmodular.high_anchor_strict_relay (d p δ w b q : ℝ)
    (hd : 0 < d) (hd7 : d ≤ 7 / 40) (hp : 0 ≤ p)
    (hcredit : (1 : ℝ) / 2 ≤ p ∨ d ≤ p * (1 - p))
    (hδ : 0 ≤ δ) (hr : δ + w ≤ 1 - d)
    (hden : 0 < δ + w) (hb : p + d ≤ b) (hq1 : 1 ≤ q)
    (hatt : q * (δ + w) = 3 * w - b - 3 * d)
    (hfail : 3 * (1 - 4 * d) < (2 * (1 - d) - b - w) * q) :
    ∀ z : ℝ, (3 : ℝ) / 4 <
      (1 - d) - δ * z - (1 - d - δ - w) * z * (1 - z) := by sorry
