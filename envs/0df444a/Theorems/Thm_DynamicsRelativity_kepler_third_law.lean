-- Prove2me | Theorems.Thm_DynamicsRelativity_kepler_third_law
-- name    : DynamicsRelativity.kepler_third_law
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-22T23:22:39.120261+00:00
-- url     : https://prove2.me/theorems/aafe398a-2bbc-4e5b-b317-ec2aac69ed83
-- title:
--   Kepler's third law: $T = 2\pi R^{3/2}/\sqrt{GM}$
-- statement:
--   **Kepler's third law (K3).** The period of the orbit is proportional to the radius$^{3/2}$.
--
--   Let a particle move under the attractive inverse-square law with $k=GM>0$ and nonvanishing angular momentum, and suppose the motion is periodic, with least period $T$. Define the **mean radius** of the orbit as the average of the closest and farthest distances from the centre of attraction,
--
--   $$ R \;=\; \tfrac12\big(r_{\min}+r_{\max}\big), $$
--
--   which for the ellipse of §4.3.1 is $\tfrac12\big(r_0/(1+e) + r_0/(1-e)\big) = r_0/(1-e^{2})$. Then
--
--   $$ T \;=\; \frac{2\pi\,R^{3/2}}{\sqrt{GM}} . $$
--
--   The source derives it by combining the constant areal rate $dA/dt=l/2$ of K2 with the area $\pi ab$ of the ellipse, and observes that the quantity appearing in the resulting formula has a natural interpretation as precisely this mean radius. Unlike K2, the third law genuinely uses the inverse-square form of the force.
--
--   **Formalization Note.** $r_{\min}$ and $r_{\max}$ are the infimum and supremum of $\lVert x(t)\rVert$ over all times, and $T$ is required to be the *least* positive period: without minimality the claim would be false, since every multiple of a period is again a period.
-- source:
--   David Tong, Dynamics and Relativity, University of Cambridge Part IA Mathematical Tripos lecture notes, Lent 2013, http://www.damtp.cam.ac.uk/user/tong/relativity.html — §4.3.2, K3, p. 61 and the displayed formula $T = 2\pi R^{3/2}/\sqrt{GM}$ with $R = \tfrac12(r_{\min}+r_{\max}) = r_0/(1-e^2)$ at the top of p. 62.

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Mathlib

open DynamicsRelativity

theorem DynamicsRelativity.kepler_third_law {k m T : ℝ} {x : ℝ → Vec}
    (hk : 0 < k) (h : KeplerMotion k m x) (hL : angularMomentum m x 0 ≠ 0)
    (hT : IsLeast {S : ℝ | 0 < S ∧ Function.Periodic x S} T) :
    T = 2 * Real.pi * (((⨅ t, ‖x t‖) + (⨆ t, ‖x t‖)) / 2) ^ (3 / 2 : ℝ) /
      Real.sqrt k := by sorry
