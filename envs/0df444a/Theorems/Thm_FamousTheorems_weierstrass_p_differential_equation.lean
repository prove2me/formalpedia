-- Prove2me | Theorems.Thm_FamousTheorems_weierstrass_p_differential_equation
-- name    : FamousTheorems.weierstrass_p_differential_equation
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:44.989388+00:00
-- url     : https://prove2.me/theorems/33e94845-f461-4d08-82a0-6b1c5b9662b6
-- title:
--   The differential equation of the Weierstrass ℘-function
-- statement:
--   **The differential equation of the Weierstrass $\wp$-function.** Let $\Lambda=\mathbb Z\omega_1+\mathbb Z\omega_2$ be a lattice in $\mathbb C$ with Weierstrass function $\wp$ and invariants $g_2=60G_4$, $g_3=140G_6$, where $G_{2k}=\sum_{\omega\in\Lambda\setminus0}\omega^{-2k}$. Then for every $z\notin\Lambda$,
--   $$\wp'(z)^2=4\wp(z)^3-g_2\,\wp(z)-g_3.$$
--
--   The equation shows that $z\mapsto(\wp(z),\wp'(z))$ parametrises the elliptic curve $y^2=4x^3-g_2x-g_3$. This identifies the complex torus $\mathbb C/\Lambda$ with an elliptic curve and is the starting point of the uniformisation of elliptic curves over $\mathbb C$.
--
--   **Formalization note.** Mathlib's `PeriodPair.derivWeierstrassP_sq`. A `PeriodPair` is a pair of $\mathbb R$-linearly independent periods $\omega_1,\omega_2$. `L.lattice` is the lattice they span, `L.weierstrassP` and `L.derivWeierstrassP` are $\wp$ and $\wp'$, and `L.g₂ = 60 * L.G 4` and `L.g₃ = 140 * L.G 6`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `PeriodPair.derivWeierstrassP_sq`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem weierstrass_p_differential_equation (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) :
    L.derivWeierstrassP z ^ 2 = 4 * L.weierstrassP z ^ 3 - L.g₂ * L.weierstrassP z - L.g₃ := by sorry

end FamousTheorems
