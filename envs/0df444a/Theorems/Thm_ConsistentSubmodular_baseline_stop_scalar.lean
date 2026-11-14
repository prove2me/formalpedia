-- Prove2me | Theorems.Thm_ConsistentSubmodular_baseline_stop_scalar
-- name    : ConsistentSubmodular.baseline_stop_scalar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:08.494078+00:00
-- url     : https://prove2.me/theorems/073aef25-619c-47b1-90f8-e2ef55c33c77
-- title:
--   Baseline stop: eligibility and credit from a large baseline
-- statement:
--   Let $A,D,\delta,w,b,q$ be real numbers with $0\le D\le A$, $\delta\ge0$, $D\le b$, $1\le q\le\tfrac32$, and
--   $$(3-q)\,w=q\,\delta+b+D.$$
--   Then both of the following hold:
--
--   1. $0\le w-(q-1)\delta-D$;
--   2. $2Aq-3(A-D)\le q\,(b+w)$.
--
--   A baseline $b$ of at least the deficit budget $D$ supplies both the eligibility and the required credit for parameters $q$ between $1$ and $\tfrac32$.
--
--   This is a scalar inequality used in the certificate constructor at the stopping row when the baseline is large.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/BaselineStop.lean#L25-L51 (`ConsistentSubmodular.baseline_stop_scalar`)

import Mathlib

theorem ConsistentSubmodular.baseline_stop_scalar (A D δ w b q : ℝ)
    (hD : 0 ≤ D) (hDA : D ≤ A) (hδ : 0 ≤ δ) (hb : D ≤ b)
    (hq1 : 1 ≤ q) (hq3 : q ≤ 3 / 2)
    (hatt : (3 - q) * w = q * δ + b + D) :
    0 ≤ w - (q - 1) * δ - D ∧
      2 * A * q - 3 * (A - D) ≤ q * (b + w) := by sorry
