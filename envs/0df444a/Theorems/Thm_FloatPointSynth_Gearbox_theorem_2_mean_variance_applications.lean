-- Prove2me | Theorems.Thm_FloatPointSynth_Gearbox_theorem_2_mean_variance_applications
-- name    : FloatPointSynth.Gearbox.theorem_2_mean_variance_applications
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T04:00:24.804221+00:00
-- url     : https://prove2.me/theorems/278a3354-76f7-472d-bfaf-1134f4733679
-- title:
--   Theorem 2 — E(n_d) = 2^d/(P_1⋯P_d), and for θ0 < π/4, V(n_d) ≤ 2^{2d+1}(1 − P_1)/(P_d²⋯P_1²)·(1 + (P_d⋯P_1)/(2^d P_1))
-- statement:
--   Let $U$ be a single-qubit unitary and $\theta_0\in[0,\pi/2]$ the angle with $\sin^2\theta_0=|U_{1,0}|^2$. For $q\ge1$ let
--   $$\varphi_q=\tan^{-1}\big(\tan^{2^{q-1}}(\theta_0)\big),\qquad P_q=\sin^4(\varphi_q)+\cos^4(\varphi_q).$$
--   For $d\ge1$ let $n_d$ be the number of applications of $U$ or $U^\dagger$ used to enact the composed gearbox circuit $C^{\circ d}(U)$ when every failed measurement is corrected and the level is retried until success (the law of Appendix A, (A1), with $n_d=2x_d$). Then
--
--   1. the expectation of $n_d$ is
--   $$\mathbb E(n_d)=\frac{2^d}{P_1\cdots P_d};$$
--   2. if $\theta_0<\pi/4$, the variance of $n_d$ obeys
--   $$\mathbb V(n_d)\le\frac{2^{2d+1}(1-P_1)}{P_d^2\cdots P_1^2}\left(1+\frac{P_d\cdots P_1}{2^dP_1}\right).$$
--
--   Since $P_q\to1$ rapidly for $\theta_0<\pi/4$, the expected number of $U,U^\dagger$ gates grows like $2^d$, and the variance bound shows the count concentrates around that order.
--
--   **Formalization Note** Mean and variance are $[0,\infty]$-valued sums over the law of $n_d$, so divergence cannot be hidden by a junk value; the mean inside the variance enters as a real number, which is legitimate because clause 1 makes it finite. The success probabilities in the law are computed from the circuit (Born rule), not set to $P_q$.
--
--   Differences from the source:
--   - reading: "the number of applications of $U$ or $U^\dagger$ used to enact $C^{\circ d}(U)$ in a given attempt" → the total number used until $C^{\circ d}(U)$ succeeds, with the law of Appendix A's (A1) and $n_d=2x_d$; reason: the paper's proof (p. 14) defines $x_d$ as the number of applications of $C^{\circ1}(U)$ "before $C^{\circ d}(U)$ is successfully implemented".
--   - encoding: real mean and variance → `ℝ≥0∞`-valued moments compared with `ENNReal.ofReal` of the paper's expressions; reason: the mean is finite (clause 1), and an `ℝ≥0∞` upper bound cannot hold vacuously for an infinite variance.
--   - encoding: $\theta_0$ defined by $\sin^2\theta_0=|U_{1,0}|^2$ → $\theta_0$ quantified with $0\le\theta_0\le\pi/2$ and that equation; reason: unique in $[0,\pi/2]$, the paper's implicit range.
-- source:
--   Wiebe and Kliuchnikov, Floating Point Representations in Quantum Circuit Synthesis, arXiv:1305.5528v3, p. 6, Theorem 2 (proof in Appendix A, pp. 14–15)

import Mathlib
import Definitions.Def_FloatPointSynth_Gearbox_Cost

namespace FloatPointSynth.Gearbox

/-- Theorem 2 (p. 6). For unitary `U`, `θ0 ∈ [0, π/2]` with `sin²θ0 = |U_{1,0}|²` and `d ≥ 1`,
the number `n_d` of applications of `U` or `U†` used to enact `C◦d(U)` satisfies
`E(n_d) = 2^d / (P_1 ⋯ P_d)`, and for `θ0 < π/4`
`V(n_d) ≤ 2^{2d+1}(1 - P_1)/(P_d² ⋯ P_1²) · (1 + (P_d ⋯ P_1)/(2^d P_1))`. -/
theorem theorem_2_mean_variance_applications (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) (θ0 : ℝ) (hθ0 : 0 ≤ θ0) (hθ1 : θ0 ≤ Real.pi / 2)
    (hθ : Real.sin θ0 ^ 2 = ‖U 1 0‖ ^ 2) (d : ℕ) (hd : 1 ≤ d) :
    pmfMean (nLaw U d) = ENNReal.ofReal (2 ^ d / ∏ q ∈ Finset.Icc 1 d, P θ0 q) ∧
    (θ0 < Real.pi / 4 →
      pmfVar (nLaw U d) ≤
        ENNReal.ofReal (2 ^ (2 * d + 1) * (1 - P θ0 1) / (∏ q ∈ Finset.Icc 1 d, P θ0 q) ^ 2 *
          (1 + (∏ q ∈ Finset.Icc 1 d, P θ0 q) / (2 ^ d * P θ0 1)))) := by sorry

end FloatPointSynth.Gearbox
