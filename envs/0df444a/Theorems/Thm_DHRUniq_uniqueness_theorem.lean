-- Prove2me | Theorems.Thm_DHRUniq_uniqueness_theorem
-- name    : DHRUniq.uniqueness_theorem
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:37:09.20754+00:00
-- url     : https://prove2.me/theorems/ca2c0957-f004-4510-be6b-bddeed480b5c
-- title:
--   Theorem 23: the uniqueness theorem for entanglement measures
-- statement:
--   Let $E$ be a functional on pure states. Then the following are equivalent:
--
--   1. $E$ satisfies (P1′), (P2), (P3) and (P4′).
--   2. $E$ satisfies (P0), (P1), (P2), (P3) and (P4).
--   3. $E$ coincides with the reduced von Neumann entropy: for every wavefunction $|\psi\rangle$ on every $\mathcal H^A\otimes\mathcal H^B$,
--
--   $$
--   E(|\psi\rangle\langle\psi|)=S_{\mathrm{vN}}(|\psi\rangle\langle\psi|)=-\operatorname{tr}_A\big((\operatorname{tr}_BP_\psi)\log_2(\operatorname{tr}_BP_\psi)\big).
--   $$
--
--   On the other hand, if $E$ satisfies (P0), (P1), (P2) and (P3), then $E$ satisfies (P5′′) and, on pure states, $E^\infty=S_{\mathrm{vN}}$:
--
--   $$
--   \lim_{n\to\infty}\frac{E(|\psi^{\otimes n}\rangle\langle\psi^{\otimes n}|)}{n}=S_{\mathrm{vN}}(|\psi\rangle\langle\psi|).
--   $$
--
--   This gives necessary and sufficient conditions for a measure of entanglement to be the entropy of the reduced state on pure states.
--
--   Differences from the source:
--   - encoding: E is a functional on pure states → E is a real function on all matrices over finite bipartite index types; reason: only its values at |ψ⟩⟨ψ| for unit ψ are read, and every functional on pure states extends to such a function
--   - encoding: finite-dimensional Hilbert spaces H^A, H^B → ℂ^a, ℂ^b for finite index types a, b with the standard basis; reason: every finite-dimensional Hilbert space is unitarily isomorphic to such a space
--   - encoding: an operation which can be realized by means of local operations and classical communications, in (P2) → IsLQCC, Definition 4; reason: the paper fixes this class: "For definiteness, in the sequel we will use LQCC operations" (p. 6)
--   - encoding: (1), (2), (3) are equivalent → (1) ⇔ (2) and (2) ⇔ (3); reason: the same statement
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, Theorem 23, pp. 17–18

import Mathlib
import Definitions.Def_DHRUniq_BipartiteFunctional
import Definitions.Def_DHRUniq_IsUnitVec
import Definitions.Def_DHRUniq_P0
import Definitions.Def_DHRUniq_P1
import Definitions.Def_DHRUniq_P1prime
import Definitions.Def_DHRUniq_P2
import Definitions.Def_DHRUniq_P3
import Definitions.Def_DHRUniq_P4
import Definitions.Def_DHRUniq_P4prime
import Definitions.Def_DHRUniq_P5dprime
import Definitions.Def_WildeQIT_EntManip_entEntropy
import Definitions.Def_WildeQIT_EntManip_tensorPowVec
import Definitions.Def_ObliviousRSP_pureState

open Filter Topology
open ObliviousRSP (pureState)
open WildeQIT.EntManip (entEntropy tensorPowVec)

namespace DHRUniq

/-- **Theorem 23, the uniqueness theorem for entanglement measures** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, Theorem 23, pp. 17–18).
Let `E` be a functional on pure states. Then the following are equivalent:
(1) `E` satisfies (P1′), (P2), (P3), and (P4′);
(2) `E` satisfies (P0), (P1), (P2), (P3), and (P4);
(3) `E` coincides with the reduced von Neumann entropy `E = S_vN`.
On the other hand, if `E` satisfies (P0), (P1), (P2), and (P3), then `E` satisfies (P5′′) and, on pure
states, `E^∞ = S_vN`.

**Formalization Note** The three conjuncts are (1) ⇔ (2), (2) ⇔ (3) and the last sentence. `E` is any
real function on matrices over all finite bipartite index types; (3) says that `E (pureState ψ)` is
`entEntropy ψ` (eq. (3)) for every unit `ψ` on every `a × b`. `E^∞ = S_vN` is the limit
`E(ψ^{⊗n})/n → S_vN(ψ)`. No hypothesis on `E` is added. -/
theorem uniqueness_theorem (E : BipartiteFunctional) :
    ((P1prime E ∧ P2 E ∧ P3 E ∧ P4prime E) ↔ (P0 E ∧ P1 E ∧ P2 E ∧ P3 E ∧ P4 E)) ∧
    ((P0 E ∧ P1 E ∧ P2 E ∧ P3 E ∧ P4 E) ↔
      ∀ ⦃a b : Type⦄ [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (ψ : a × b → ℂ),
        IsUnitVec ψ → E (pureState ψ) = entEntropy ψ) ∧
    (P0 E ∧ P1 E ∧ P2 E ∧ P3 E →
      P5dprime E ∧
        ∀ ⦃a b : Type⦄ [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (ψ : a × b → ℂ),
          IsUnitVec ψ →
          Tendsto (fun n : ℕ => E (pureState (tensorPowVec ψ n)) / n) atTop
            (𝓝 (entEntropy ψ))) := by sorry

end DHRUniq
