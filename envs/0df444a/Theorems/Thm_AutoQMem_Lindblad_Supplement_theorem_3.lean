-- Prove2me | Theorems.Thm_AutoQMem_Lindblad_Supplement_theorem_3
-- name    : AutoQMem.Lindblad.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:48:15.022527+00:00
-- url     : https://prove2.me/theorems/204deb12-25bc-4012-a140-764790f3c3c7
-- title:
--   Theorem 3: the synchronous 4D Toom channel is a syndrome-based, $R$-local, translation-invariant quantum $2Cme^{-cL}$-memory through round $m$ below a noise threshold
-- statement:
--   For $L\ge1$ let $\mathcal C_L$ be the 4D toric code of linear size $L$, $a^{(X)},a^{(Z)}$ its two 4D Toom update rules, and for a synchronous Pauli noise layer $N_*$ let
--   $$Q^{\mathrm{Toom}}_*=N_*\circ\hat a^{Z}_{a^{(Z)}*}\circ\hat a^{X}_{a^{(X)}*}$$
--   be the quantum lift of the two Toom rules followed by $N_*$. There exist constants $\eta_c,C,c>0$ and $R\in\mathbb N$, independent of $L$, and readout decoders $\mathrm{Dec}^L_X,\mathrm{Dec}^L_Z$ for each $L$, such that for every $L\ge1$ and every noise layer $N_*$:
--
--   1. $Q^{\mathrm{Toom}}_*$ is a syndrome-based quantum channel;
--   2. $Q^{\mathrm{Toom}}_*$ is $R$-local;
--   3. $Q^{\mathrm{Toom}}_*$ commutes with every lattice translation under which the rates $\theta_{P,i}$ of $N_*$ are invariant;
--   4. if $N_*$ has rate $\eta<\eta_c$, then for every designated logical qubit and every $m\in\mathbb N$,
--   $$F_{\min}\big[(Q^{\mathrm{Toom}}_*)^r\big]\ \ge\ 1-2Cm\,e^{-cL}\qquad\text{for every }0\le r\le m .$$
--
--   Hence, for a fixed target error, the number of synchronous rounds for which the 4D toric code under the lifted Toom rule remains a quantum memory grows exponentially in $L$.
--
--   Differences from the source:
--   - encoding: n-qubit CSS code with a designated logical qubit (Definitions 2.1, 2.8–2.9) → n = n'+1 qubits, the designated qubit is qubit 0, and the conjugate-pair facts H_Z ℓ_X = 0, H_X ℓ_Z = 0, ℓ_X·ℓ_Z = 1 are explicit (the base mission's LogicalQubit); reason: the encoding unitary is arbitrary, so naming qubit 0 loses no generality; same instances
--   - reading: readout decoders not named in the statement; the proof takes 'the decoders of the recovery step in Ahn's analysis' (p. 49), which the paper does not define → the decoders are existential, one pair per L, chosen before the noise layer, the logical qubit and m; reason: Reading D: a universally quantified decoder makes the statement false (a bad decoder destroys memory); Ahn's decoders depend on L only
--   - reading: the two positively oriented boundary edges e⁺_{i,μ}, e⁺_{i,ν} of a plaquette; the Z predicate 'on the dual lattice' → e⁺_{i,μ} = (x + u_μ, {ν}), e⁺_{i,ν} = (x + u_ν, {μ}) for i = (x, {μ, ν}); the Z rule reads the 3-cubes (x, S ∪ {κ}), κ ∉ S; reason: Reading T1 (Toom's positively oriented neighbours, p. 47); the near-side reading is its image under the reflection x ↦ −x, which preserves the code, the noise class, the logical qubits and the decoders
--   - reading: [H_X x]_e = Σ_{i⊃e} x_i, [H_Z x]_c = Σ_{i⊂c} x_i → incidence counted with multiplicity mod 2 (the cellular boundary maps ∂_2, ∂_3), on cells (x, S) enumerated by Fin; reason: identical to the face relation for L ≥ 2; for L = 1 the two opposite faces coincide and the cellular boundary is the standard meaning, keeping H_X H_Zᵀ = 0
--   - reading: 'the encoded system' (the designated logical qubit is left implicit) → the bound holds for every designated logical qubit; reason: the proof fixes an arbitrary logical qubit and uses only the linearity of μ_σ (p. 50)
--   - generalization: translationally invariant whenever N_* is → for every single y ∈ (ℤ/Lℤ)⁴ with θ_{P, y+i} = θ_{P,i}, Q^Toom_*(U_y ρ U_y†) = U_y Q^Toom_*(ρ) U_y† for every ρ; reason: per-translation equivariance; when N_* is invariant under every translation it gives the source's full translation invariance of Q^Toom_* (the lifts commute with every translation, p. 50)
--   - encoding: linear size L, quantum q(m, L)-memory through round m → every L ≥ 1 ([NeZero L]); pointwise bound 1 − 2·C·m·exp(−c·L) ≤ F_min for every r ≤ m; reason: same statement; C absorbs small L
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Theorem 3, pp. 30–31 (PDF pp. 32–33); proof §6, pp. 47–50 (PDF pp. 49–52)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_Supplement_SyndromeChannel
import Definitions.Def_AutoQMem_Lindblad_Supplement_IsQuantumMemoryThrough
import Definitions.Def_AutoQMem_Lindblad_Supplement_NoiseLayer
import Definitions.Def_AutoQMem_Lindblad_Supplement_IsRLocalChannel
import Definitions.Def_AutoQMem_Lindblad_Supplement_quantumLift
import Definitions.Def_AutoQMem_Lindblad_Supplement_toomRule
import Definitions.Def_AutoQMem_Lindblad_Supplement_translation
open Matrix

namespace AutoQMem.Lindblad.Supplement

open AutoQMem.Lindblad

/-- **Theorem 3 (Synchronous 4D Toom quantum memory).** Drechsler, Oreg, Aharonov, *Autonomous Quantum
Memories from Classical Stochastic Processes*, arXiv:2610.05589 (PDF of 2026-11-03), Theorem 3,
pp. 30–31 (PDF 32–33); proof §6, p. 50 (PDF 52).

For the 4D toric code of linear size `L`, let `N_*` be a synchronous Pauli noise layer of rate `η`.
There exist constants `η_c, C, c > 0`, independent of `L`, and a syndrome-based quantum channel
`Q^Toom_*`, `R`-local for some `R` independent of `L`, such that if `η < η_c`, the encoded system
evolving under `Q^Toom_*` is a quantum `q(m, L)`-memory through round `m`, with
`q(m, L) = 2Cm e^{−cL}`. The channel is the quantum lift of the two 4D Toom update rules followed by
`N_*`, and is translationally invariant whenever `N_*` is.

**Formalization Note.**
* The channel is fixed by the paper: `Q^Toom_* = N_* ∘ â^Z_{a(Z)} ∘ â^X_{a(X)}` (Definition 5.4,
  Lemma 5.6, Definitions 6.1–6.2, Reading T1 for the positively oriented edges); the theorem asserts
  that it is syndrome-based (Definition 2.35), `R`-local (Definition 2.38) and translation
  invariant for every noise layer, and a memory below `η_c`.
* Reading D: the readout decoders are "the decoders of the recovery step in Ahn's analysis"
  (p. 49), which the paper does not define; they are existential, one pair per `L`, chosen before
  the noise, the round count and the logical qubit.
* `η_c, C, c, R` are chosen before `L`; the memory bound holds for every `L ≥ 1`, every noise layer
  of rate `η < η_c`, every designated logical qubit and every `m`. -/
theorem theorem_3 :
    ∃ ηc Cc c : ℝ, 0 < ηc ∧ 0 < Cc ∧ 0 < c ∧ ∃ R : ℕ,
    ∃ (DX : ∀ (L : ℕ) [NeZero L], Decoder (toricCode L).HX)
      (DZ : ∀ (L : ℕ) [NeZero L], Decoder (toricCode L).HZ),
    ∀ (L : ℕ) [NeZero L] (N : NoiseLayer (toricN' L + 1)),
      IsSyndromeBased (toricCode L)
        (N.apply ∘ liftZ (toricCode L) (toomZ L) ∘ liftX (toricCode L) (toomX L)) ∧
      IsRLocalChannel (toricCode L) R
        (N.apply ∘ liftZ (toricCode L) (toomZ L) ∘ liftX (toricCode L) (toomX L)) ∧
      (∀ y : Fin 4 → ZMod L,
        (∀ i, N.θX (plaqTransl L y i) = N.θX i ∧ N.θY (plaqTransl L y i) = N.θY i ∧
          N.θZ (plaqTransl L y i) = N.θZ i) →
        ∀ ρ, (N.apply ∘ liftZ (toricCode L) (toomZ L) ∘ liftX (toricCode L) (toomX L))
            (permConj (plaqTransl L y) ρ) =
          permConj (plaqTransl L y)
            ((N.apply ∘ liftZ (toricCode L) (toomZ L) ∘ liftX (toricCode L) (toomX L)) ρ)) ∧
      ∀ η : ℝ, N.HasRate η → η < ηc → ∀ (Q : LogicalQubit (toricCode L)) (m : ℕ),
        IsQuantumMemoryThrough Q (DX L) (DZ L)
          (fun r => (N.apply ∘ liftZ (toricCode L) (toomZ L) ∘ liftX (toricCode L) (toomX L))^[r])
          m (2 * Cc * m * Real.exp (-c * L)) := by sorry

end AutoQMem.Lindblad.Supplement
