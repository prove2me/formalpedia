-- Prove2me | Theorems.Thm_ConsistentSubmodular_threshold_attainer_eligible
-- name    : ConsistentSubmodular.threshold_attainer_eligible
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:43.061229+00:00
-- url     : https://prove2.me/theorems/44b6e7a7-d314-4fb4-b2a5-bebce4baaa72
-- title:
--   Threshold anchors: attaining stages have positive actual eligibility
-- statement:
--   Let $q,p,d,\delta,w,b\in\mathbb{R}$ with
--
--   * $0<q\le1$;
--   * $0\le d\le\tfrac{319}{1600}$ and $p\ge0$;
--   * (strong credit) $\tfrac12\le p$ or $d\le p(1-p)$;
--   * $\delta\ge0$ and $b\ge p+d$;
--   * (attainment) $(3-q)\,w=q\,\delta+b+3d$.
--
--   Then
--   $$0\;<\;1-4d-q\,\delta-\Bigl(q-\tfrac{q^2}{4}\Bigr)(1-d-\delta-w).$$
--
--   At the rational anchor threshold $d\le 319/1600$, every low-parameter attaining stage thus has a strictly positive actual eligibility margin. The lemma supports the low-parameter test of the checkpoint constructor in Appendix B.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/EligibilityThreshold.lean#L85-L105 (`ConsistentSubmodular.threshold_attainer_eligible`)

import Mathlib

theorem ConsistentSubmodular.threshold_attainer_eligible (q p d δ w b : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) (hd : 0 ≤ d) (hd319 : d ≤ 319 / 1600)
    (hp : 0 ≤ p) (hcredit : (1 : ℝ) / 2 ≤ p ∨ d ≤ p * (1 - p))
    (hδ : 0 ≤ δ) (hb : p + d ≤ b)
    (hatt : (3 - q) * w = q * δ + b + 3 * d) :
    0 < 1 - 4 * d - q * δ - (q - q ^ 2 / 4) * (1 - d - δ - w) := by sorry
