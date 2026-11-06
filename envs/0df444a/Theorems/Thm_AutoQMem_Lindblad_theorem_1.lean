-- Prove2me | Theorems.Thm_AutoQMem_Lindblad_theorem_1
-- name    : AutoQMem.Lindblad.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:02:20.421045+00:00
-- url     : https://prove2.me/theorems/41d7a349-0228-404f-ba75-01eafccb8693
-- title:
--   Theorem 1: sector processes that $q_X$-, $q_Z$-remember give a quantum $(q_X+q_Z)$-memory, and a quantum $\epsilon$-memory makes both sectors $\epsilon$-remember
-- statement:
--   Consider an $n$-qubit CSS code with parity checks $H_X,H_Z$, a designated logical qubit (encoding unitary $U$, bare logicals $\bar X=X^{\ell_X}$, $\bar Z=Z^{\ell_Z}$), readout decoders $\mathrm{Dec}_X,\mathrm{Dec}_Z$, and a syndrome-based Lindbladian $\mathcal L(t)$ with Schrödinger propagator $\mathcal W_*(t,0)$. Let $\xi^{(X)}_t$, $\xi^{(Z)}_t$ be the induced sector error processes (backward transition operators $M^{(X)}$, $M^{(Z)}$) and $b_X,b_Z$ the logical-error indicators. Fix $t\ge0$ and real numbers $q_X,q_Z,\epsilon$.
--
--   1. If the X- and Z-sector processes respectively $q_X$- and $q_Z$-remember $b_X$ and $b_Z$ up to time $t$, i.e.
--   $$\Pr\bigl[b_X(\xi^{(X)}_a)\neq b_X(\xi^{(X)}_0)\bigr]\le q_X,\qquad \Pr\bigl[b_Z(\xi^{(Z)}_a)\neq b_Z(\xi^{(Z)}_0)\bigr]\le q_Z\qquad(0\le a\le t),$$
--   then the encoded system is a quantum $(q_X+q_Z)$-memory up to time $t$:
--   $$F_{\min}[\mathcal W_*(a,0)]\ge1-(q_X+q_Z)\qquad(0\le a\le t).$$
--   2. Conversely, if $F_{\min}[\mathcal W_*(a,0)]\ge1-\epsilon$ for all $a\in[0,t]$, then each sector process $\epsilon$-remembers its logical-error indicator up to time $t$.
--
--   For syndrome-based Lindbladian dynamics, quantum memory of the designated logical qubit is thus equivalent, up to a factor of two, to memory of the two induced classical sector processes. In part 1 the sector processes may be started at any one pair of stored codewords $(w_0^X,w_0^Z)$; in part 2 the conclusion holds for every stored codeword.
--
--   Differences from the source:
--   - encoding: stabilizer generators S^X_a, S^Z_b of the CSS code defined by H_X, H_Z → S^X_a = X^{row a of H_X}, S^Z_b = Z^{row b of H_Z}, without phases; reason: the standard CSS generating set defined by the parity-check matrices (Definition 2.1)
--   - encoding: X̄ ∈ {I,X}^{⊗n}, Z̄ ∈ {I,Z}^{⊗n} a conjugate pair of CSS logical Pauli strings with supports ℓ_X, ℓ_Z → X̄ = X^{ℓ_X}, Z̄ = Z^{ℓ_Z} with H_Z ℓ_X = 0, H_X ℓ_Z = 0, ℓ_X · ℓ_Z = 1; reason: these are exactly the facts the paper derives from "conjugate pair of CSS logical Pauli strings" (proof of Claim 2.11, p. 17)
--   - encoding: designated input qubit Q, H = H_Q ⊗ H_rest, |0⟩_rest → Q is qubit 0, H_rest is qubits 1, …, n−1, |0⟩_rest is the all-zero basis vector; n = n′ + 1 ≥ 1; reason: the encoding unitary U is arbitrary, so naming qubit 0 as Q loses no instance; Q needs one qubit
--   - encoding: Dec : Σ → 𝔽₂ⁿ → Dec a total function on 𝔽₂^m with H Dec(s) = s on im H and Dec(0) = 0; reason: values off Σ are never used
--   - reading: Definition 2.22 leaves the time dependence of H(t) and f_{P,i,α}(t) open; W_*(t,0) and M(t,0) are the solutions of (40) and (51) → H(t) and every f_{P,i,α}(t) measurable on [0,∞) and bounded on every [0,T]; W and M are any solutions of (40), (51) in integrated, entrywise form with integrable integrand; reason: the paper's Remark 2.26 regularity; without some regularity the propagator need not exist (rate 1/t), and under it the integral equations have exactly one solution; no continuity or time independence is assumed
--   - encoding: probabilities and expectations over the sector error process ξ_t = χ_t ⊕ w_0 with χ_0 = w_0 → Σ_y M(t,0)(w_0, y)·[b(y ⊕ w_0) ≠ b(0)] (flipProb) and Σ_y M(t,0)(w_0, y)·(−1)^{b(y ⊕ w_0) ⊕ b(0)}, with the stored codeword w_0 explicit; reason: Reading R2: by (50) M(t,0)(w_0, y) = Pr[χ_t = y | χ_0 = w_0], and only the one-time law of ξ_t enters
--   - encoding: α ranges over a finite index set (possibly depending on P and i) → one finite index type ι shared by all (P, i); reason: a (P, i)-dependent finite family is padded with zero syndrome functions, which add nothing to (31) or (32)
--   - encoding: syndrome eigenvalue A(s) of A ∈ A_X at s ∈ Σ_X (eq. (6)) → Tr(A Π^X_s)/Tr(Π^X_s) (eigX), likewise eigZ; reason: equal to A(s) whenever A ∈ A_X and s ∈ Σ_X, the only arguments at which the statement uses it
--   - encoding: inf_{a∈[0,t]} F_min ≥ 1 − ϵ and sup_{a∈[0,t]} Pr[…] ≤ q (eqs. (28)–(29)); F_min a minimum over unit vectors → pointwise bounds for every a ∈ [0, t]; F_min an infimum over ψ ∈ ℂ² with Σ|ψ_i|² = 1; reason: Reading R3: these are equivalent formulations (the propagator is CPTP, so the infimum over the compact unit sphere is attained)
--   - encoding: F(ψ; W_*) = ⟨ψ| E_L[W_*](|ψ⟩⟨ψ|) |ψ⟩ → its real part; reason: W_*(a, 0) is CPTP, so E_L is a channel and the value is real; the real part changes nothing
--   - encoding: "up to time t", readout interval I = [0, t] → 0 ≤ t is a hypothesis; reason: for t < 0 the interval [0, t] is empty and both directions hold vacuously, so no instance is lost
--   - reading: "the X- and Z-sector processes respectively q_X- and q_Z-remember" (processes started at stored codewords, Definition 2.28); conclusion "each induced sector process ϵ-remembers" → (i) assumes remembering for one stored pair (w_0^X, w_0^Z); (ii) concludes it for every stored codeword; reason: by Claim 2.33 the law of the error process does not depend on w_0; assuming one pair and concluding for all is the strongest reading
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Theorem 1, p. 29 (PDF p. 31); proof §4.6, pp. 40–41 (PDF pp. 42–43)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_IsQuantumMemoryUpTo
import Definitions.Def_AutoQMem_Lindblad_SyndromeLindbladian_genX
import Definitions.Def_AutoQMem_Lindblad_IsPropagator
import Definitions.Def_AutoQMem_Lindblad_flipProb
open Matrix

namespace AutoQMem.Lindblad

/-- **Theorem 1 (Fully Autonomous quantum–classical memory equivalence).** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Theorem 1,
p. 29 (PDF 31); proof §4.6, pp. 40–41 (PDF 42–43).

Consider a CSS code with a designated logical qubit evolving under a syndrome-based Lindbladian
`L(t)`, with induced sector error processes `ξ^{(X)}_t`, `ξ^{(Z)}_t`.
1. If the X- and Z-sector processes respectively `q_X`- and `q_Z`-remember their logical-error
   indicators `b_X` and `b_Z` up to time `t`, then the encoded system is a quantum
   `(q_X + q_Z)`-memory up to time `t`.
2. Conversely, if the encoded system is a quantum `ε`-memory up to time `t`, then each induced
   sector process `ε`-remembers its logical-error indicator up to time `t`.

**Formalization Note.**
* Every CSS code (`n = n' + 1 ≥ 1` qubits, dependent rows allowed), every designated logical qubit
  `Q` (encoding `U`, `ℓ_X`, `ℓ_Z`), every pair of readout decoders (no linearity, no
  locality), every syndrome-based Lindbladian with time-dependent `H(t)`, `f_{P,i,α}(t)`
  (Reading R1: measurable, locally bounded), every `t ≥ 0`, all real `q_X, q_Z, ε`.
* `W` is the propagator `W_*(·, 0)` (solution of (40)); `W a` is the physical channel at readout
  time `a ∈ [0, t]`. `M_X`, `M_Z` are the backward transition operators (solutions of (51)).
* Reading R2: the sector process starts at a stored codeword `w_0`, and `flipProb` is
  `Pr[b(ξ_a) ≠ b(ξ_0)]`. In (i) remembering is assumed for one stored pair `(w_0^X, w_0^Z)`; in
  (ii) it is concluded for every stored codeword. -/
theorem theorem_1 {n' mX mZ : ℕ} (C : CSSCode (n' + 1) mX mZ) (Q : LogicalQubit C)
    (DX : Decoder C.HX) (DZ : Decoder C.HZ) {ι : Type} [Fintype ι]
    (L : SyndromeLindbladian C ι)
    (W : ℝ → Op (n' + 1) → Op (n' + 1)) (hW : IsPropagator L W)
    (MX MZ : ℝ → Matrix (Fin (n' + 1) → ZMod 2) (Fin (n' + 1) → ZMod 2) ℝ)
    (hMX : IsBackwardPropagator L.genX MX) (hMZ : IsBackwardPropagator L.genZ MZ)
    (t : ℝ) (ht : 0 ≤ t) (qX qZ ε : ℝ) :
    (∀ w0X ∈ C.codeX, ∀ w0Z ∈ C.codeZ,
      RemembersUpTo (flipProb MX C.HX Q.lX DX w0X) t qX →
      RemembersUpTo (flipProb MZ C.HZ Q.lZ DZ w0Z) t qZ →
      IsQuantumMemoryUpTo Q DX DZ W t (qX + qZ)) ∧
    (IsQuantumMemoryUpTo Q DX DZ W t ε →
      (∀ w0X ∈ C.codeX, RemembersUpTo (flipProb MX C.HX Q.lX DX w0X) t ε) ∧
      (∀ w0Z ∈ C.codeZ, RemembersUpTo (flipProb MZ C.HZ Q.lZ DZ w0Z) t ε)) := by sorry

end AutoQMem.Lindblad
