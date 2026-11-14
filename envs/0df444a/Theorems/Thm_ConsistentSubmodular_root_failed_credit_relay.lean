-- Prove2me | Theorems.Thm_ConsistentSubmodular_root_failed_credit_relay
-- name    : ConsistentSubmodular.root_failed_credit_relay
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:08.080937+00:00
-- url     : https://prove2.me/theorems/71109d94-0ea9-4897-9c95-6e0003e657fd
-- title:
--   Failure of the root credit threshold yields a strictly safe relay
-- statement:
--   Let $\delta,w,v,v_c,k$ be real numbers with $\delta\ge0$, $w\ge0$, $\delta+w>0$, $k>0$, $w\le v\le v_c$,
--   $$k\,(\delta+w)=4w-v,\qquad v_c<2-\frac3k.$$
--   Then both of the following hold:
--
--   1. $\delta<w\,(1-w)$;
--   2. for every real $z$,
--   $$\frac34\;<\;1-\delta z-(1-\delta-w)\,z\,(1-z).$$
--
--   Failure of the root credit threshold thus makes every attaining row a strictly safe relay. The positivity of $\delta+w$ excludes omitted zero rows.
--
--   This is a scalar step of the relay analysis in the certificate construction for the $3/4$ bound.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/RelayScalar.lean#L19-L51 (`ConsistentSubmodular.root_failed_credit_relay`)

import Mathlib

theorem ConsistentSubmodular.root_failed_credit_relay (δ w v vc k : ℝ)
    (_hδ : 0 ≤ δ) (_hw : 0 ≤ w) (hden : 0 < δ + w)
    (hk : 0 < k) (hvw : w ≤ v) (hvc : v ≤ vc)
    (hatt : k * (δ + w) = 4 * w - v)
    (hfail : vc < 2 - 3 / k) :
    δ < w * (1 - w) ∧
      ∀ z : ℝ, (3 : ℝ) / 4 <
        1 - δ * z - (1 - δ - w) * z * (1 - z) := by sorry
