-- Prove2me | Theorems.Thm_AutoQMem_Lindblad_proposition_6
-- name    : AutoQMem.Lindblad.proposition_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:01:32.479796+00:00
-- url     : https://prove2.me/theorems/f6d58794-75fd-439d-b9a7-c62437e8659e
-- title:
--   Proposition 6: $\langle T_\sigma,\mathcal W^*(t,0)(T_\sigma)\rangle_{\mathrm{code}}=1-2\Pr[b_\sigma(\xi_t)\neq b_\sigma(\xi_0)]$
-- statement:
--   Let $\mathcal L(t)$ be a syndrome-based Lindbladian for a CSS code with Heisenberg propagator $\mathcal W^*(t,0)$, let $T_X,T_Z$ be the decoded logical observables of a designated logical qubit, $b_X,b_Z$ the logical-error indicators, and $\xi^{(X)}_t$, $\xi^{(Z)}_t$ the induced sector error processes. Then for every $\sigma\in\{X,Z\}$ and every $t\ge0$,
--   $$\langle T_\sigma,\mathcal W^*(t,0)(T_\sigma)\rangle_{\mathrm{code}}=\mathbb E\Bigl[(-1)^{b_\sigma(\xi^{(\sigma)}_t)\oplus b_\sigma(\xi^{(\sigma)}_0)}\Bigr]=1-2\Pr\bigl[b_\sigma(\xi^{(\sigma)}_t)\neq b_\sigma(\xi^{(\sigma)}_0)\bigr].$$
--   Both equalities hold for every stored codeword $w_0\in C_\sigma$ from which the sector process is started.
--
--   This identifies the quantum decoded-logical autocorrelation with the classical probability of a logical readout error at the same time.
--
--   Differences from the source:
--   - encoding: stabilizer generators S^X_a, S^Z_b of the CSS code defined by H_X, H_Z → S^X_a = X^{row a of H_X}, S^Z_b = Z^{row b of H_Z}, without phases; reason: the standard CSS generating set defined by the parity-check matrices (Definition 2.1)
--   - encoding: X̄ ∈ {I,X}^{⊗n}, Z̄ ∈ {I,Z}^{⊗n} a conjugate pair of CSS logical Pauli strings with supports ℓ_X, ℓ_Z → X̄ = X^{ℓ_X}, Z̄ = Z^{ℓ_Z} with H_Z ℓ_X = 0, H_X ℓ_Z = 0, ℓ_X · ℓ_Z = 1; reason: these are exactly the facts the paper derives from "conjugate pair of CSS logical Pauli strings" (proof of Claim 2.11, p. 17)
--   - encoding: designated input qubit Q, H = H_Q ⊗ H_rest, |0⟩_rest → Q is qubit 0, H_rest is qubits 1, …, n−1, |0⟩_rest is the all-zero basis vector; n = n′ + 1 ≥ 1; reason: the encoding unitary U is arbitrary, so naming qubit 0 as Q loses no instance; Q needs one qubit
--   - encoding: Dec : Σ → 𝔽₂ⁿ → Dec a total function on 𝔽₂^m with H Dec(s) = s on im H and Dec(0) = 0; reason: values off Σ are never used
--   - reading: Definition 2.22 leaves the time dependence of H(t) and f_{P,i,α}(t) open; W_*(t,0) and M(t,0) are the solutions of (40) and (51) → H(t) and every f_{P,i,α}(t) measurable on [0,∞) and bounded on every [0,T]; W and M are any solutions of (40), (51) in integrated, entrywise form with integrable integrand; reason: the paper's Remark 2.26 regularity; without some regularity the propagator need not exist (rate 1/t), and under it the integral equations have exactly one solution; no continuity or time independence is assumed
--   - encoding: probabilities and expectations over the sector error process ξ_t = χ_t ⊕ w_0 with χ_0 = w_0 → Σ_y M(t,0)(w_0, y)·[b(y ⊕ w_0) ≠ b(0)] (flipProb) and Σ_y M(t,0)(w_0, y)·(−1)^{b(y ⊕ w_0) ⊕ b(0)}, with the stored codeword w_0 explicit; reason: Reading R2: by (50) M(t,0)(w_0, y) = Pr[χ_t = y | χ_0 = w_0], and only the one-time law of ξ_t enters
--   - encoding: α ranges over a finite index set (possibly depending on P and i) → one finite index type ι shared by all (P, i); reason: a (P, i)-dependent finite family is padded with zero syndrome functions, which add nothing to (31) or (32)
--   - encoding: Heisenberg propagator W^*(t,0) = W_*(t,0)^* → hsAdj (W t), the trace-pairing adjoint of the Schrödinger propagator; reason: the definition of the adjoint on p. 22 and eq. (43)
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Proposition 6, eq. (77), p. 29 (PDF p. 31); proof §4.5, p. 38 (PDF p. 40)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit_TX
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit_codeInner
import Definitions.Def_AutoQMem_Lindblad_SyndromeLindbladian_genX
import Definitions.Def_AutoQMem_Lindblad_IsPropagator
import Definitions.Def_AutoQMem_Lindblad_hsAdj
import Definitions.Def_AutoQMem_Lindblad_flipProb
open Matrix

namespace AutoQMem.Lindblad

/-- **Proposition 6 (Asynchronous quantum-to-classical reduction).** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Proposition 6,
eq. (77), p. 29 (PDF 31); proof §4.5, p. 38 (PDF 40).

For every `σ ∈ {X, Z}` and every `t ≥ 0`,
`⟨T_σ, W^*(t, 0)(T_σ)⟩_code = E[(−1)^{b_σ(ξ_t) ⊕ b_σ(ξ_0)}] = 1 − 2 Pr[b_σ(ξ_t) ≠ b_σ(ξ_0)]`.

**Formalization Note (Readings R1, R2).** `W^*(t, 0) = hsAdj (W t)` for the solution `W` of (40);
`M_X`, `M_Z` solve (51) for `G_X`, `G_Z`. The sector process starts at an arbitrary stored
codeword `w_0 ∈ C_X` (resp. `C_Z`), the error process is `ξ_t = χ_t ⊕ w_0`, and the expectation
is `Σ_y M(t,0)(w_0, y) (−1)^{b(y ⊕ w_0) ⊕ b(0)}`; the probability is `flipProb`. -/
theorem proposition_6 {n' mX mZ : ℕ} (C : CSSCode (n' + 1) mX mZ) (Q : LogicalQubit C) (DX : Decoder C.HX) (DZ : Decoder C.HZ)
    {ι : Type} [Fintype ι] (L : SyndromeLindbladian C ι)
    (W : ℝ → Op (n' + 1) → Op (n' + 1)) (hW : IsPropagator L W)
    (MX MZ : ℝ → Matrix (Fin (n' + 1) → ZMod 2) (Fin (n' + 1) → ZMod 2) ℝ)
    (hMX : IsBackwardPropagator L.genX MX) (hMZ : IsBackwardPropagator L.genZ MZ)
    (t : ℝ) (ht : 0 ≤ t) :
    (∀ w0 ∈ C.codeX,
      Q.codeInner (Q.TX DX) (hsAdj (W t) (Q.TX DX)) =
          ∑ y, (MX t w0 y : ℂ) * (-1 : ℂ) ^
            (decodedValue C.HX Q.lX DX (y + w0) + decodedValue C.HX Q.lX DX 0).val ∧
        Q.codeInner (Q.TX DX) (hsAdj (W t) (Q.TX DX)) =
          ((1 - 2 * flipProb MX C.HX Q.lX DX w0 t : ℝ) : ℂ)) ∧
    (∀ w0 ∈ C.codeZ,
      Q.codeInner (Q.TZ DZ) (hsAdj (W t) (Q.TZ DZ)) =
          ∑ y, (MZ t w0 y : ℂ) * (-1 : ℂ) ^
            (decodedValue C.HZ Q.lZ DZ (y + w0) + decodedValue C.HZ Q.lZ DZ 0).val ∧
        Q.codeInner (Q.TZ DZ) (hsAdj (W t) (Q.TZ DZ)) =
          ((1 - 2 * flipProb MZ C.HZ Q.lZ DZ w0 t : ℝ) : ℂ)) := by sorry

end AutoQMem.Lindblad
