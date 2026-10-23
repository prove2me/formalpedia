-- Prove2me | Theorems.Thm_FloatPointSynth_Gearbox_P_monotone
-- name    : FloatPointSynth.Gearbox.P_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T04:00:39.799012+00:00
-- url     : https://prove2.me/theorems/bd62d5b9-7c31-4292-9d27-3c436db5d8b9
-- title:
--   Appendix A, p. 15 — P_q is a monotonically increasing function of q for θ0 < π/4
-- statement:
--   Let $0\le\theta_0<\pi/4$, and for $q\ge1$ let $\varphi_q=\tan^{-1}\big(\tan^{2^{q-1}}(\theta_0)\big)$ and $P_q=\sin^4(\varphi_q)+\cos^4(\varphi_q)$. Then for every $q\ge1$
--   $$P_q\le P_{q+1},$$
--   with strict inequality when $\theta_0>0$.
--
--   The monotonicity is used to unfold the variance recursion (A7) into the bound (A8).
--
--   Differences from the source:
--   - reading: "$P_q$ is a monotonically increasing function of $q$" → $P_q\le P_{q+1}$ for all $q\ge1$, and $P_q<P_{q+1}$ when $\theta_0>0$; reason: at $\theta_0=0$ every $P_q=1$, so the strict reading is false there; both readings are stated where true.
--   - encoding: $\theta_0<\pi/4$ → $0\le\theta_0<\pi/4$; reason: $\theta_0$ is the angle in $[0,\pi/2]$ with $\sin^2\theta_0=|U_{1,0}|^2$ (p. 5).
-- source:
--   Wiebe and Kliuchnikov, Floating Point Representations in Quantum Circuit Synthesis, arXiv:1305.5528v3, p. 15, Appendix A (before Eq. (A8))

import Mathlib
import Definitions.Def_FloatPointSynth_Gearbox_Cost

namespace FloatPointSynth.Gearbox

/-- Appendix A, p. 15: for `0 ≤ θ0 < π/4`, `P_q` is a monotonically increasing function of
`q ≥ 1`: `P_q ≤ P_{q+1}`, strictly when `θ0 > 0` (at `θ0 = 0` every `P_q` equals `1`). -/
theorem P_monotone (θ0 : ℝ) (hθ0 : 0 ≤ θ0) (hθ1 : θ0 < Real.pi / 4) (q : ℕ) (hq : 1 ≤ q) :
    P θ0 q ≤ P θ0 (q + 1) ∧ (0 < θ0 → P θ0 q < P θ0 (q + 1)) := by sorry

end FloatPointSynth.Gearbox
