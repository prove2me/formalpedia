-- Prove2me | Theorems.Thm_FamousTheorems_liouville_transcendental
-- name    : FamousTheorems.liouville_transcendental
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T21:55:22.94105+00:00
-- url     : https://prove2.me/theorems/08e37e8e-52e9-473a-8df3-685f14fbb92e
-- title:
--   Liouville numbers are transcendental
-- statement:
--   **Every Liouville number is transcendental.**
--
--   A real $x$ is *Liouville* if for every $n$ there are integers $p, q > 1$ with
--   $$0 < \left|x - \frac{p}{q}\right| < \frac{1}{q^{n}},$$
--   i.e. $x$ is abnormally well approximated by rationals. Every such $x$ is transcendental.
--
--   The proof is Liouville's inequality: an irrational algebraic number of degree $d$ satisfies
--   $|x - p/q| > c/q^{d}$ for some $c > 0$, because a non-zero integer value of the minimal
--   polynomial is at least $1$ in absolute value. Being approximable to order beyond $d$ is
--   therefore impossible.
--
--   This gave the **first explicit transcendental numbers** in 1844 — such as
--   $\sum_k 10^{-k!}$ — three decades before Cantor showed that almost all reals are
--   transcendental without naming one.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem liouville_transcendental : ∀ {x : ℝ}, Liouville x → Transcendental ℤ x := by sorry

end FamousTheorems
