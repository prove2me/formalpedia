-- Prove2me | Theorems.Thm_FloatPointSynth_Gearbox_corollary_1
-- name    : FloatPointSynth.Gearbox.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:59:43.702182+00:00
-- url     : https://prove2.me/theorems/05ec317d-6e53-47e0-a4a2-271772988032
-- title:
--   Corollary 1 — on success the composed gearbox C◦d(U) enacts e^{−i tan⁻¹(tan^{2^d}(θ0))X}
-- statement:
--   Let $U$ be a single-qubit unitary and $\theta_0\in[0,\pi/2]$ the angle with $\sin^2\theta_0=|U_{1,0}|^2$. For every $d\ge1$, the composed gearbox circuit $C^{\circ d}(U)$ of Definition 1 enacts, when each of its measurements gives $0$,
--   $$C^{\circ d}(U)=e^{-i\tan^{-1}\left(\tan^{2^d}(\theta_0)\right)X},$$
--   where the angle is read as $\pi/2$ when $\theta_0=\pi/2$.
--
--   Composition thus squares the tangent of the rotation angle at every level, so $d$ levels turn a rotation by about $\theta_0$ into one by about $\tan^{2^d}\theta_0$. The success probability is deliberately not part of this statement.
--
--   **Formalization Note** $C^{\circ d}(U)$ is the recursively defined success unitary: $C^{\circ0}(U)=U$ and $C^{\circ(n+1)}(U)$ is the normalized outcome-$0$ block of the one-ancilla gearbox fed with $C^{\circ n}(U)$.
--
--   Differences from the source:
--   - encoding: $\tan^{-1}(\tan^{2^d}\theta_0)$ at $\theta_0=\pi/2$ → `composedAngle θ0 d`, equal to $\pi/2$ when $\cos\theta_0=0$; reason: Lean's `Real.tan (π/2)` is $0$; the paper's value is $\tan^{-1}(\infty)=\pi/2$.
--   - encoding: "$C^{\circ d}:|\psi\rangle\to e^{-i\tan^{-1}(\tan^{2^d}\theta_0)X}|\psi\rangle$ if each measurement yields 0" → equality of the success unitary `composed U d` (normalized outcome-$0$ block, defined recursively) with the rotation matrix; reason: this is how Definition 1's recursion acts on success; normalization removes the success amplitude.
--   - encoding: $\theta_0$ defined by $\sin^2\theta_0=|U_{1,0}|^2$ → $\theta_0$ quantified with $0\le\theta_0\le\pi/2$ and that equation; reason: unique in $[0,\pi/2]$, the paper's implicit range.
-- source:
--   Wiebe and Kliuchnikov, Floating Point Representations in Quantum Circuit Synthesis, arXiv:1305.5528v3, p. 5, Corollary 1 (with Definition 1)

import Mathlib
import Definitions.Def_FloatPointSynth_Gearbox_Circuit

namespace FloatPointSynth.Gearbox

/-- Corollary 1 (p. 5). For unitary `U` and `θ0 ∈ [0, π/2]` with `sin²θ0 = |U_{1,0}|²`, the
composed gearbox `C◦d(U)` enacts `e^{-i tan⁻¹(tan^{2^d}(θ0)) X}` when every measurement gives `0`,
for every `d ≥ 1`. -/
theorem corollary_1 (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (θ0 : ℝ) (hθ0 : 0 ≤ θ0) (hθ1 : θ0 ≤ Real.pi / 2) (hθ : Real.sin θ0 ^ 2 = ‖U 1 0‖ ^ 2)
    (d : ℕ) (hd : 1 ≤ d) :
    composed U d = rotX (composedAngle θ0 d) := by sorry

end FloatPointSynth.Gearbox
