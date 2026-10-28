-- Prove2me | Theorems.Thm_CommitOpen_Benign_pure_trace_distance
-- name    : CommitOpen.Benign.pure_trace_distance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:44.43928+00:00
-- url     : https://prove2.me/theorems/9bf55eeb-ce8d-4bd6-9950-5dd22afb6256
-- title:
--   Proof of Lemma 4.3, p. 11 — trace distance of two pure states is √(1 − |⟨ψ|φ⟩|²)
-- statement:
--   Let $|\varphi\rangle$ and $|\psi\rangle$ be unit vectors of a finite-dimensional complex Hilbert space. Then
--   $$\delta\big(|\varphi\rangle\langle\varphi|,\,|\psi\rangle\langle\psi|\big)=\sqrt{1-|\langle\psi|\varphi\rangle|^2},$$
--   where $\delta(\rho,\sigma)=\tfrac12\operatorname{tr}|\rho-\sigma|$ is the trace distance.
--
--   In the proof of Lemma 4.3 this converts the distance between Bob's real state and its projection onto the "good" subspace into the norm of the discarded component.
-- source:
--   Damgård, Fehr, Lunemann, Salvail & Schaffner, Improving the Security of Quantum Protocols via Commit-and-Open, arXiv:0902.3918v4, p. 11, proof of Lemma 4.3 (first display)

import Mathlib
import Definitions.Def_CommitOpen_Benign_Model

namespace CommitOpen.Benign

theorem pure_trace_distance {ι : Type} [Fintype ι] [DecidableEq ι] (φ ψ : EuclideanSpace ℂ ι)
    (hφ : ‖φ‖ = 1) (hψ : ‖ψ‖ = 1) :
    traceDistance (pureState φ) (pureState ψ) = Real.sqrt (1 - ‖inner ℂ ψ φ‖ ^ 2) := by sorry

end CommitOpen.Benign
