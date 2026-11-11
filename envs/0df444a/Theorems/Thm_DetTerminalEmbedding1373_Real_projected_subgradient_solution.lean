-- Prove2me | Theorems.Thm_DetTerminalEmbedding1373_Real_projected_subgradient_solution
-- name    : DetTerminalEmbedding1373.Real.projected_subgradient_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:28:35.649739+00:00
-- url     : https://prove2.me/theorems/901ddc99-0679-4af0-8b69-5954de14bd3e
-- title:
--   Lemma 5.2 — deterministic projected subgradient solution
-- statement:
--   Let $x_i\in E_d$ be a nonempty family of nonzero vectors, $V=\{\pm x_i/\|x_i\|\}$, and let $A:E_d\to E_m$ have additive convex-hull distortion at most $\eta$ on $V$, where $0<\eta\le1/2$. For $\|u\|\le1$ form $a_i=A(x_i/\|x_i\|)$, $c_i=\langle u,x_i/\|x_i\|\rangle$ and $f(w)=\max_i|\langle w,a_i\rangle-c_i|$. Set $h=\eta/4$ and $T=\lceil4/\eta^2\rceil$. The fixed solver program halts and returns the earliest best iterate with index below $T$, and
--
--   $$w\in B_2^m,\qquad f(w)\le2\eta,\qquad t\le500000\,Nm\eta^{-2}.$$
--
--   Its output agrees with the explicitly defined projected subgradient sequence and its recorded earliest best index. Feasibility is a conclusion of the geometric hypotheses, not an assumed optimum witness. The universal constant precedes all inputs. This gives a computed extension vector and a charged query-time bound.
--
--   Differences from the source:
--   - encoding: Euclidean spaces and finite indexed vectors or signs → EuclideanSpace over Fin indices and Boolean signs; reason: the Euclidean norm and every real coordinate are retained, with +1 represented by true
--   - generalization: nearest-terminal differences and the normalized ambient query vector in (33) → any nonzero finite vector family and any u of norm at most one with the same convex-hull guarantee; reason: this includes the source setup and Section 6, whose terminal-span query vector may have norm strictly below one
--   - encoding: O(nmη⁻²) arithmetic operations within T iterations → the explicit solver program with actual work at most 500000 Nmη⁻² and the same exact h and T; reason: the source has n−1 active constraints, represented by N; the charged loop derivation fixes a single constant independent of all inputs
--   - encoding: the algorithm returns a vector w → the program output additionally equals the explicitly defined sequence's earliest best iterate solve a c η, and the program records that index; reason: bookkeeping identities that tie the executed program to the source's iteration (36) and its return rule on p. 20; they hold for the source's algorithm and exclude no source instance
-- source:
--   Vladimir Braverman, Kuan Cheng, Jiaqing Zhu, STOC 2027 submission #1373 (October 2026), pp. 18–20, Lemma 5.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1373.pdf

import Definitions.Def_DetTerminalEmbedding1373_Real_execution

set_option autoImplicit false
open scoped ENNReal

namespace DetTerminalEmbedding1373.Real

/-- Lemma 5.2, pp. 18–20. The norm-bounded u form includes the terminal-span
specialization in Section 6. Feasibility is not an input witness. -/
theorem projected_subgradient_solution :
    ∃ C : ℕ, C = 500000 ∧ Admissible solverProgram ∧
    ∀ (N d m : ℕ) (hN : 0 < N) (x : Fin N → E d), (∀ i, x i ≠ 0) →
    ∀ (A : E d →ₗ[ℝ] E m) (η : ℝ), 0 < η → η ≤ 1 / 2 →
      ConvexHullDistortion A (signedDirections x) η →
    ∀ u : E d, ‖u‖ ≤ 1 →
      let a := correlationVectors A x
      let c := correlationScalars x u
      let s := solverInput a c η
      let t := haltTime solverProgram s
      let w := computedSolution a c η
      Halts solverProgram s t ∧
      (t : ℝ) ≤ (C : ℝ) * (N : ℝ) * (m : ℝ) / η ^ 2 ∧
      w = solve a c η ∧
      (finalState solverProgram s).ints 4 0 = (bestIterateIndex a c η : ℤ) ∧
      bestIterateIndex a c η < solverIterations η ∧
      w ∈ unitBall m ∧ objective a c w ≤ 2 * η := by sorry

end DetTerminalEmbedding1373.Real
