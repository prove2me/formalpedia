-- Prove2me | Theorems.Thm_AutoQMem_Lindblad_lemma_4_17
-- name    : AutoQMem.Lindblad.lemma_4_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:59:00.307191+00:00
-- url     : https://prove2.me/theorems/c1c15b7f-435a-4caa-b633-a326e7a4f81f
-- title:
--   Lemma 4.17: $\mathcal W^*(t,0)(\bar PO\bar P)=\bar P\,\mathcal W^*(t,0)(O)\,\bar P$ for $\bar P\in\{\bar X,\bar Z\}$
-- statement:
--   For every syndrome-based Lindbladian and every $t\ge0$, the Heisenberg propagator satisfies
--   $$\mathcal W^*(t,0)(\bar PO\bar P)=\bar P\,\mathcal W^*(t,0)(O)\,\bar P,\qquad \bar P\in\{\bar X,\bar Z\},$$
--   for every operator $O$.
--
--   This verifies the covariance hypothesis of Lemma 4.15 for continuous-time syndrome-based dynamics.
--
--   Differences from the source:
--   - encoding: stabilizer generators S^X_a, S^Z_b of the CSS code defined by H_X, H_Z → S^X_a = X^{row a of H_X}, S^Z_b = Z^{row b of H_Z}, without phases; reason: the standard CSS generating set defined by the parity-check matrices (Definition 2.1)
--   - encoding: X̄ ∈ {I,X}^{⊗n}, Z̄ ∈ {I,Z}^{⊗n} a conjugate pair of CSS logical Pauli strings with supports ℓ_X, ℓ_Z → X̄ = X^{ℓ_X}, Z̄ = Z^{ℓ_Z} with H_Z ℓ_X = 0, H_X ℓ_Z = 0, ℓ_X · ℓ_Z = 1; reason: these are exactly the facts the paper derives from "conjugate pair of CSS logical Pauli strings" (proof of Claim 2.11, p. 17)
--   - encoding: designated input qubit Q, H = H_Q ⊗ H_rest, |0⟩_rest → Q is qubit 0, H_rest is qubits 1, …, n−1, |0⟩_rest is the all-zero basis vector; n = n′ + 1 ≥ 1; reason: the encoding unitary U is arbitrary, so naming qubit 0 as Q loses no instance; Q needs one qubit
--   - reading: Definition 2.22 leaves the time dependence of H(t) and f_{P,i,α}(t) open; W_*(t,0) and M(t,0) are the solutions of (40) and (51) → H(t) and every f_{P,i,α}(t) measurable on [0,∞) and bounded on every [0,T]; W and M are any solutions of (40), (51) in integrated, entrywise form with integrable integrand; reason: the paper's Remark 2.26 regularity; without some regularity the propagator need not exist (rate 1/t), and under it the integral equations have exactly one solution; no continuity or time independence is assumed
--   - encoding: α ranges over a finite index set (possibly depending on P and i) → one finite index type ι shared by all (P, i); reason: a (P, i)-dependent finite family is padded with zero syndrome functions, which add nothing to (31) or (32)
--   - encoding: Heisenberg propagator W^*(t,0) = W_*(t,0)^* → hsAdj (W t), the trace-pairing adjoint of the Schrödinger propagator; reason: the definition of the adjoint on p. 22 and eq. (43)
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Lemma 4.17, eq. (121), p. 40 (PDF p. 42); proof pp. 40–41 (PDF pp. 42–43)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit
import Definitions.Def_AutoQMem_Lindblad_IsPropagator
import Definitions.Def_AutoQMem_Lindblad_hsAdj
open Matrix

namespace AutoQMem.Lindblad

/-- **Lemma 4.17 (Logical-Pauli covariance of syndrome-based Lindbladian evolution).** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03),
Lemma 4.17, eq. (121), p. 40 (PDF 42); proof pp. 40–41 (PDF 42–43).

For every syndrome-based Lindbladian and every `t ≥ 0`, the Heisenberg-picture propagator satisfies
`W^*(t, 0)(P̄ O P̄) = P̄ W^*(t, 0)(O) P̄` for `P̄ ∈ {X̄, Z̄}` and every `O ∈ B(H)`.

**Formalization Note.** `W^*(t, 0) = hsAdj (W t)` for any solution `W` of (40) (Reading R1). -/
theorem lemma_4_17 {n' mX mZ : ℕ} (C : CSSCode (n' + 1) mX mZ) (Q : LogicalQubit C) {ι : Type} [Fintype ι] (L : SyndromeLindbladian C ι)
    (W : ℝ → Op (n' + 1) → Op (n' + 1)) (hW : IsPropagator L W) (t : ℝ) (ht : 0 ≤ t) :
    (∀ O : Op (n' + 1),
      hsAdj (W t) (pauliX Q.lX * O * pauliX Q.lX) = pauliX Q.lX * hsAdj (W t) O * pauliX Q.lX) ∧
    (∀ O : Op (n' + 1),
      hsAdj (W t) (pauliZ Q.lZ * O * pauliZ Q.lZ) = pauliZ Q.lZ * hsAdj (W t) O * pauliZ Q.lZ) := by sorry

end AutoQMem.Lindblad
