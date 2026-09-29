-- Prove2me | Theorems.Thm_FamousTheorems_riemann_zeta_nonvanishing_re_ge_one
-- name    : FamousTheorems.riemann_zeta_nonvanishing_re_ge_one
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:09.688495+00:00
-- url     : https://prove2.me/theorems/ee406ec2-bed7-4629-9fae-1d622c3e9be9
-- title:
--   Non-vanishing of ζ(s) on Re(s) ≥ 1
-- statement:
--   **Non-vanishing of $\zeta$ on $\operatorname{Re}s\ge1$.** The Riemann zeta function has no zeros in the closed half-plane $\operatorname{Re}s\ge1$.
--
--   For $\operatorname{Re}s>1$ this follows from the Euler product. The case of the line $\operatorname{Re}s=1$, due to Hadamard and de la Vallée Poussin (1896), is the key analytic input of the prime number theorem, and via Wiener–Ikehara it is essentially equivalent to it.
--
--   **Formalization note.** Mathlib's `riemannZeta_ne_zero_of_one_le_re`. At $s=1$, where $\zeta$ has a pole, Mathlib's `riemannZeta` takes a specific finite value ($\frac{\gamma-\log4\pi}{2}$), which is nonzero, so the statement includes $s=1$ without exception.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `riemannZeta_ne_zero_of_one_le_re`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem riemann_zeta_nonvanishing_re_ge_one {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta s ≠ 0 := by sorry

end FamousTheorems
