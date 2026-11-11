-- Prove2me | Theorems.Thm_ConstOverheadCompile_Main_proposition_16
-- name    : ConstOverheadCompile.Main.proposition_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:01:53.648206+00:00
-- url     : https://prove2.me/theorems/86999b8f-a7b5-41ee-b11a-19d0f19f7e91
-- title:
--   Proposition 16: the phase-halving circuit applies $R(\theta)$ to both inputs and returns the catalyst
-- statement:
--   Let $\theta\in\mathbb R$ and let $\psi,\phi\in\mathbb C^2$. The phase-halving circuit of Figure 1 (right) satisfies
--   $$R(\theta)|+\rangle\otimes|\psi\rangle\otimes|\phi\rangle\otimes|0\rangle\ \longmapsto\ R(\theta)|+\rangle\otimes R(\theta)|\psi\rangle\otimes R(\theta)|\phi\rangle\otimes|0\rangle ,$$
--   as an exact equality of vectors, with no global phase.
--
--   The catalyst $R(\theta)|+\rangle$ is returned unchanged, so one $R(2\theta)$ gate yields two applications of $R(\theta)$; this is the conversion (13) used to replenish the bank in Algorithm 1.
--
--   Differences from the source:
--   - generalization: single-qubit states $|\psi\rangle$, $|\phi\rangle$ → arbitrary vectors in $\mathbb C^2$; reason: the circuit is linear, and states are a special case.
-- source:
--   Chenyi Zhang, Xinyu Tan, Robin Kothari, David Gosset, Craig Gidney, Quantum circuit compilation with constant overhead, STOC 2027 submission #397 (October 2026), source.pdf SHA-256 b848604016de1821f5f693c59f328e0b2a9e535bca0b37bb664e6f40dbe3681f, p.17, Appendix B, Proposition 16, Eq. (71); circuit: p.6, Figure 1 (right)

import Mathlib
import Definitions.Def_ConstOverheadCompile_Main_Gadgets

namespace ConstOverheadCompile.Main

open QAlgorithms

/-- Proposition 16, p.17 (Eq. (71)): the phase-halving circuit of Figure 1 (right) maps
`R(θ)|+⟩ ⊗ ψ ⊗ φ ⊗ |0⟩` to `R(θ)|+⟩ ⊗ R(θ)ψ ⊗ R(θ)φ ⊗ |0⟩`, exactly, for every real `θ` and
all single-qubit vectors `ψ, φ`. -/
theorem proposition_16 (θ : ℝ) (ψ φ : Bool → ℂ) :
    (phaseHalving θ).unitary.mulVec (vec4 (resourceVec θ) ψ φ (basisVec false)) =
      vec4 (resourceVec θ) ((rot θ).mulVec ψ) ((rot θ).mulVec φ) (basisVec false) := by sorry

end ConstOverheadCompile.Main
