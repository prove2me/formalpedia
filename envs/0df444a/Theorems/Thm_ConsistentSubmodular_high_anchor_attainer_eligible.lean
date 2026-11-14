-- Prove2me | Theorems.Thm_ConsistentSubmodular_high_anchor_attainer_eligible
-- name    : ConsistentSubmodular.high_anchor_attainer_eligible
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:23.375407+00:00
-- url     : https://prove2.me/theorems/b4bf896a-e131-44a9-8ed6-c840ecae2859
-- title:
--   High anchors: every attaining stage is eligible
-- statement:
--   Let $q,p,d,\delta,w,b\in\mathbb{R}$ with
--
--   * $1\le q\le 2$;
--   * $0\le d\le \tfrac{7}{40}$ and $d\le p$;
--   * $\delta\ge 0$ and $b\ge p+d$;
--   * (attainment) $(3-q)\,w=q\,\delta+b+3d$.
--
--   Then
--   $$0\;\le\;1-4d-q\,\delta-\Bigl(q-\tfrac{q^2}{4}\Bigr)(1-d-\delta-w).$$
--
--   The right-hand side is the actual eligibility margin of the stage that attains the ratio $q$; the statement says it is nonnegative whenever the anchor is high ($d\le 7/40$). It is a scalar lemma used in the constructor tests of the deterministic certificate (Appendix B).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/HighAnchor.lean#L50-L68 (`ConsistentSubmodular.high_anchor_attainer_eligible`)

import Mathlib

theorem ConsistentSubmodular.high_anchor_attainer_eligible (q p d δ w b : ℝ)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hd : 0 ≤ d) (hd7 : d ≤ 7 / 40)
    (hpd : d ≤ p) (hδ : 0 ≤ δ) (hb : p + d ≤ b)
    (hatt : (3 - q) * w = q * δ + b + 3 * d) :
    0 ≤ 1 - 4 * d - q * δ - (q - q ^ 2 / 4) * (1 - d - δ - w) := by sorry
