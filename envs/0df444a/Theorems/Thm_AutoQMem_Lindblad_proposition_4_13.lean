-- Prove2me | Theorems.Thm_AutoQMem_Lindblad_proposition_4_13
-- name    : AutoQMem.Lindblad.proposition_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:01:07.65301+00:00
-- url     : https://prove2.me/theorems/9d9ba1e9-dc09-4540-a71f-343e9a2a9ee7
-- title:
--   Proposition 4.13: $\Phi_X\circ\mathcal L^*(t)=G_X(t)\circ\Phi_X$ and $\Phi_X\circ\mathcal W^*(t,0)=M^{(X)}(t,0)\circ\Phi_X$ on $V_X$
-- statement:
--   Let $\mathcal L(t)$ be a syndrome-based Lindbladian with Heisenberg propagator $\mathcal W^*(t,0)$, and let $M^{(X)}(t,0)$ be the backward transition operator of the induced X-sector generator $G_X(t)$. For every $t\ge0$ and every $O\in V_X$:
--
--   1. $\mathcal L^*(t)(O)\in V_X$ and
--   $$\Phi_X(\mathcal L^*(t)(O))=G_X(t)\,\Phi_X(O);$$
--   2. $\mathcal W^*(t,0)(O)\in V_X$ and
--   $$\Phi_X(\mathcal W^*(t,0)(O))=M^{(X)}(t,0)\,\Phi_X(O).$$
--
--   The analogous statements hold in the Z sector with $V_Z$, $\Phi_Z$, $G_Z$, $M^{(Z)}$.
--
--   The classical Markov chain reproduces exactly the Heisenberg evolution of the sector subspace.
--
--   Differences from the source:
--   - encoding: stabilizer generators S^X_a, S^Z_b of the CSS code defined by H_X, H_Z → S^X_a = X^{row a of H_X}, S^Z_b = Z^{row b of H_Z}, without phases; reason: the standard CSS generating set defined by the parity-check matrices (Definition 2.1)
--   - encoding: X̄ ∈ {I,X}^{⊗n}, Z̄ ∈ {I,Z}^{⊗n} a conjugate pair of CSS logical Pauli strings with supports ℓ_X, ℓ_Z → X̄ = X^{ℓ_X}, Z̄ = Z^{ℓ_Z} with H_Z ℓ_X = 0, H_X ℓ_Z = 0, ℓ_X · ℓ_Z = 1; reason: these are exactly the facts the paper derives from "conjugate pair of CSS logical Pauli strings" (proof of Claim 2.11, p. 17)
--   - encoding: designated input qubit Q, H = H_Q ⊗ H_rest, |0⟩_rest → Q is qubit 0, H_rest is qubits 1, …, n−1, |0⟩_rest is the all-zero basis vector; n = n′ + 1 ≥ 1; reason: the encoding unitary U is arbitrary, so naming qubit 0 as Q loses no instance; Q needs one qubit
--   - reading: Definition 2.22 leaves the time dependence of H(t) and f_{P,i,α}(t) open; W_*(t,0) and M(t,0) are the solutions of (40) and (51) → H(t) and every f_{P,i,α}(t) measurable on [0,∞) and bounded on every [0,T]; W and M are any solutions of (40), (51) in integrated, entrywise form with integrable integrand; reason: the paper's Remark 2.26 regularity; without some regularity the propagator need not exist (rate 1/t), and under it the integral equations have exactly one solution; no continuity or time independence is assumed
--   - encoding: α ranges over a finite index set (possibly depending on P and i) → one finite index type ι shared by all (P, i); reason: a (P, i)-dependent finite family is padded with zero syndrome functions, which add nothing to (31) or (32)
--   - encoding: syndrome eigenvalue A(s) of A ∈ A_X at s ∈ Σ_X (eq. (6)) → Tr(A Π^X_s)/Tr(Π^X_s) (eigX), likewise eigZ; reason: equal to A(s) whenever A ∈ A_X and s ∈ Σ_X, the only arguments at which the statement uses it
--   - generalization: Φ_X : V_X → ℝ^{Ω_X} → Φ_X(O)(e) = (−1)^{ℓ_X·e}(X̄O)(H_X e), complex valued, for O = X̄A with any A in the complex algebra A_X; reason: A_X is a complex algebra and Φ_X is extended linearly; for Hermitian A the values are real and the statement specializes to the paper's
--   - encoding: Heisenberg propagator W^*(t,0) = W_*(t,0)^* → hsAdj (W t), the trace-pairing adjoint of the Schrödinger propagator; reason: the definition of the adjoint on p. 22 and eq. (43)
--   - generalization: (106) states the intertwining identity → also concludes W^*(t,0)(O) ∈ V_X; reason: the invariance is drawn in the proposition's Figure 2 and used as (109); dropping the extra conclusion gives the printed statement
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Proposition 4.13, eqs. (105)–(106), Figure 2, p. 37 (PDF p. 39); proof Appendix B, p. 66 (PDF p. 68)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit_PhiX__43fab1
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit_inVX
import Definitions.Def_AutoQMem_Lindblad_SyndromeLindbladian_genX
import Definitions.Def_AutoQMem_Lindblad_IsPropagator
import Definitions.Def_AutoQMem_Lindblad_hsAdj
open Matrix

namespace AutoQMem.Lindblad

/-- **Proposition 4.13 (Intertwining of propagators).** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Proposition 4.13,
eqs. (105)–(106), p. 37 (PDF 39); proof Appendix B, p. 66 (PDF 68).

`V_X` is invariant under `L*(t)` for every `t ≥ 0`, and for `O ∈ V_X`,
`Φ_X(L*(t)(O)) = G_X(t) Φ_X(O)`. Consequently the propagators intertwine:
`Φ_X(W^*(t, 0)(O)) = M^{(X)}(t, 0) Φ_X(O)` (with `W^*(t, 0)(O) ∈ V_X`, Figure 2). The analogous
statements hold in the Z sector.

**Formalization Note.** `W^*(t, 0) = hsAdj (W t)` for any solution `W` of (40), and `M` is
any solution of (51) for `G_X` (Reading R1). `Φ_X` is complex valued and the real matrices
`G_X(t)`, `M(t, 0)` act on it entrywise. -/
theorem proposition_4_13 {n' mX mZ : ℕ} (C : CSSCode (n' + 1) mX mZ) (Q : LogicalQubit C) {ι : Type} [Fintype ι] (L : SyndromeLindbladian C ι) :
    (∀ t : ℝ, 0 ≤ t → ∀ O : Op (n' + 1), Q.inVX O →
      Q.inVX (L.genAdj t O) ∧
        Q.PhiX (L.genAdj t O) = fun e => ∑ e', (L.genX t e e' : ℂ) * Q.PhiX O e') ∧
    (∀ (W : ℝ → Op (n' + 1) → Op (n' + 1))
        (MX : ℝ → Matrix (Fin (n' + 1) → ZMod 2) (Fin (n' + 1) → ZMod 2) ℝ),
      IsPropagator L W → IsBackwardPropagator L.genX MX →
      ∀ t : ℝ, 0 ≤ t → ∀ O : Op (n' + 1), Q.inVX O →
        Q.inVX (hsAdj (W t) O) ∧
          Q.PhiX (hsAdj (W t) O) = fun e => ∑ e', (MX t e e' : ℂ) * Q.PhiX O e') ∧
    (∀ t : ℝ, 0 ≤ t → ∀ O : Op (n' + 1), Q.inVZ O →
      Q.inVZ (L.genAdj t O) ∧
        Q.PhiZ (L.genAdj t O) = fun e => ∑ e', (L.genZ t e e' : ℂ) * Q.PhiZ O e') ∧
    (∀ (W : ℝ → Op (n' + 1) → Op (n' + 1))
        (MZ : ℝ → Matrix (Fin (n' + 1) → ZMod 2) (Fin (n' + 1) → ZMod 2) ℝ),
      IsPropagator L W → IsBackwardPropagator L.genZ MZ →
      ∀ t : ℝ, 0 ≤ t → ∀ O : Op (n' + 1), Q.inVZ O →
        Q.inVZ (hsAdj (W t) O) ∧
          Q.PhiZ (hsAdj (W t) O) = fun e => ∑ e', (MZ t e e' : ℂ) * Q.PhiZ O e') := by sorry

end AutoQMem.Lindblad
