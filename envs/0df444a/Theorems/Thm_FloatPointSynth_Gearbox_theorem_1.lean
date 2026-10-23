-- Prove2me | Theorems.Thm_FloatPointSynth_Gearbox_theorem_1
-- name    : FloatPointSynth.Gearbox.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:59:34.452309+00:00
-- url     : https://prove2.me/theorems/d61f6693-298c-4bed-9864-f3c80b327468
-- title:
--   Theorem 1 — on outcome 0 the gearbox circuit enacts e^{−iX tan⁻¹(tan²θ)} with probability cos⁴θ + sin⁴θ; other outcomes enact e^{iπX/4}
-- statement:
--   Let $d\ge1$, let $U^1,\dots,U^d$ be single-qubit unitaries, and let $\theta\in[0,\pi/2]$ be the angle with
--   $$\sin^2\theta=|U^1_{1,0}|^2\cdots|U^d_{1,0}|^2 .$$
--   Run the gearbox circuit $C^{(d)}(U^1,\dots,U^d)$ on $|0^{\otimes d}\rangle|\psi\rangle$ and measure the ancillas, and write $\beta_j(\psi)$ for the unnormalized target state left by outcome $j\in\{0,1\}^d$. Then:
--
--   1. for every $\psi\in\mathbb C^2$,
--   $$\beta_0(\psi)=\sqrt{\cos^4\theta+\sin^4\theta}\;e^{-iX\tan^{-1}(\tan^2\theta)}\,\psi ,$$
--   with $\tan^{-1}(\tan^2\theta)=\pi/2$ at $\theta=\pi/2$;
--   2. for every normalized $\psi$, outcome $0$ has probability $\|\beta_0(\psi)\|^2=\cos^4\theta+\sin^4\theta$;
--   3. for every outcome $j\ne0$ there is a scalar $c_j\in\mathbb C$, independent of $\psi$, with $\beta_j(\psi)=c_j\,e^{i\pi X/4}\psi$ for all $\psi$.
--
--   So on success the circuit enacts an $X$-rotation through the angle $\tan^{-1}(\tan^2\theta)$, and every failure enacts the Clifford rotation $e^{i\pi X/4}$, whatever the gates $U^\ell$ are; this is what makes the circuit repeatable until success.
--
--   **Formalization Note** The rotation is $e^{-i\varphi X}=\cos\varphi\,\mathbb 1-i\sin\varphi\,X$. The scalar $c_j$ may be $0$ (an outcome of probability $0$).
--
--   Differences from the source:
--   - encoding: $\tan^{-1}(\tan^2\theta)$ at $\theta=\pi/2$, i.e. $\tan^{-1}(\infty)$ → `gearAngle θ`, equal to $\pi/2$ when $\cos\theta=0$; reason: Lean's `Real.tan (π/2)` is $0$; the paper's value is $\pi/2$, and the circuit then enacts $-iX=e^{-i(\pi/2)X}$.
--   - reading: "the circuit enacts the transformation $|0^{\otimes d}\rangle|\psi\rangle\mapsto e^{-iX\tan^{-1}(\tan^2\theta)}|\psi\rangle$" given outcome $0$ → the outcome-$0$ branch equals $\sqrt{\cos^4\theta+\sin^4\theta}\,e^{-iX\tan^{-1}(\tan^2\theta)}\psi$ exactly; reason: the post-measurement state is the normalized branch; the stated equality (no extra phase) is the paper's Eq. (1), p. 3, and implies the transformation.
--   - reading: "all other measurement outcomes result in the transformation $|\psi\rangle\to e^{i\pi X/4}|\psi\rangle$" → for each $j\ne0$ a scalar $c_j$ independent of $\psi$ (possibly $0$) with $\beta_j(\psi)=c_j e^{i\pi X/4}\psi$; reason: a transformation up to normalization and global phase is a fixed operator multiple; outcomes of probability $0$ have $c_j=0$.
--   - encoding: $\theta$ defined by $\sin^2\theta=\prod_\ell|U^\ell_{1,0}|^2$ → $\theta$ quantified with $0\le\theta\le\pi/2$ and that equation; reason: the relation determines $\theta$ uniquely in $[0,\pi/2]$, the paper's implicit range.
--   - encoding: "$d$ control qubits" (Fig. 1, p. 2) → hypothesis $1\le d$; reason: the source's circuit has at least one ancilla; the degenerate $d=0$ register is excluded (the statement also holds there, so nothing is lost).
-- source:
--   Wiebe and Kliuchnikov, Floating Point Representations in Quantum Circuit Synthesis, arXiv:1305.5528v3, p. 2, Theorem 1 (proof p. 3, Eq. (1))

import Mathlib
import Definitions.Def_FloatPointSynth_Gearbox_Circuit

namespace FloatPointSynth.Gearbox

open Matrix Complex

/-- Theorem 1 (p. 2). For unitary `U¹, …, U^d` and `θ ∈ [0, π/2]` with
`sin²θ = |U¹_{1,0}|² ⋯ |U^d_{1,0}|²`: (a) on outcome `0` the gearbox circuit leaves
`√(cos⁴θ + sin⁴θ) · e^{-iX tan⁻¹(tan²θ)} |ψ⟩`; (b) for a normalized `|ψ⟩` this outcome has
probability `cos⁴θ + sin⁴θ`; (c) every other outcome `j` leaves a fixed scalar multiple
(independent of `|ψ⟩`) of `e^{iπX/4} |ψ⟩`. -/
theorem theorem_1 (d : ℕ) (hd : 1 ≤ d) (Us : Fin d → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ ℓ, Us ℓ ∈ Matrix.unitaryGroup (Fin 2) ℂ) (θ : ℝ) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ Real.pi / 2) (hθ : Real.sin θ ^ 2 = ∏ ℓ, ‖Us ℓ 1 0‖ ^ 2) :
    (∀ ψ : Fin 2 → ℂ, branch Us 0 ψ =
        ((Real.sqrt (Real.cos θ ^ 4 + Real.sin θ ^ 4) : ℝ) : ℂ) • (rotX (gearAngle θ) *ᵥ ψ)) ∧
    (∀ ψ : Fin 2 → ℂ, ∑ s, ‖ψ s‖ ^ 2 = 1 →
        ∑ s, ‖branch Us 0 ψ s‖ ^ 2 = Real.cos θ ^ 4 + Real.sin θ ^ 4) ∧
    (∀ j : Fin d → Fin 2, j ≠ 0 → ∃ c : ℂ, ∀ ψ : Fin 2 → ℂ,
        branch Us j ψ = c • (rotX (-(Real.pi / 4)) *ᵥ ψ)) := by sorry

end FloatPointSynth.Gearbox
