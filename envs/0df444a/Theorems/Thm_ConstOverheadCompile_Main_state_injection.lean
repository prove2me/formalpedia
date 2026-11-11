-- Prove2me | Theorems.Thm_ConstOverheadCompile_Main_state_injection
-- name    : ConstOverheadCompile.Main.state_injection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:01:50.465941+00:00
-- url     : https://prove2.me/theorems/65140882-87b7-4a98-ac42-41ec1e5a0670
-- title:
--   §2, Eq. (12): the state-injection gadget applies $R(\theta)$, using $R(2\theta)$ only on outcome 1
-- statement:
--   Let $\theta\in\mathbb R$ and let $\psi\in\mathbb C^2$. Run the state-injection gadget of Figure 1 (left) on $|\psi\rangle\otimes R(\theta)|+\rangle$. The gadget has exactly two branches:
--
--   1. on measurement outcome $0$ it applies only the CNOT, and the post-measurement vector is
--   $$\tfrac{1}{\sqrt2}\,R(\theta)|\psi\rangle\otimes|0\rangle ;$$
--   2. on measurement outcome $1$ it applies the CNOT and the correction $R(2\theta)$, and the post-measurement vector is
--   $$\tfrac{e^{i\theta}}{\sqrt2}\,R(\theta)|\psi\rangle\otimes|1\rangle .$$
--
--   For a state $|\psi\rangle$ each outcome therefore occurs with probability $1/2$, the data wire ends in $R(\theta)|\psi\rangle$ up to a global phase on both branches, and the gate $R(2\theta)$ is used exactly on outcome $1$. This is the resource conversion $R(\theta)|+\rangle+\tfrac12R(2\theta)\Rightarrow R(\theta)$ of Eq. (12), which drives the recursion of Algorithm 1.
--
--   Differences from the source:
--   - generalization: a single-qubit state $|\psi\rangle$ → any vector $\psi\in\mathbb C^2$; reason: the gadget is linear, and unit vectors are a special case.
--   - encoding: "adaptively implements $R(\theta)$ … with probability 1/2 … uses $R(2\theta)$" → the two branch operators applied to $|\psi\rangle\otimes R(\theta)|+\rangle$, outcome 0 listed first, with coefficients $1/\sqrt2$ and $e^{i\theta}/\sqrt2$; reason: the probabilities and the channel follow from these vectors.
-- source:
--   Chenyi Zhang, Xinyu Tan, Robin Kothari, David Gosset, Craig Gidney, Quantum circuit compilation with constant overhead, STOC 2027 submission #397 (October 2026), source.pdf SHA-256 b848604016de1821f5f693c59f328e0b2a9e535bca0b37bb664e6f40dbe3681f, p.6, §2, Figure 1 (left) and Eq. (12)

import Mathlib
import Definitions.Def_ConstOverheadCompile_Main_Gadgets

namespace ConstOverheadCompile.Main

open QAlgorithms

/-- §2, p.6, Figure 1 (left) and Eq. (12): the state-injection gadget, run on `|ψ⟩ ⊗ R(θ)|+⟩`,
has exactly two branches. On outcome 0 (one gate, CNOT) the post-measurement vector is
`(1/√2) R(θ)|ψ⟩ ⊗ |0⟩`; on outcome 1 (CNOT and the correction `R(2θ)`) it is
`(e^{iθ}/√2) R(θ)|ψ⟩ ⊗ |1⟩`. Each branch vector has squared Euclidean norm
`(‖ψ false‖² + ‖ψ true‖²)/2`, hence probability `1/2` for a normalized input state. On both
branches the data wire carries `R(θ)|ψ⟩` up to a global phase. -/
theorem state_injection (θ : ℝ) (ψ : Bool → ℂ) :
    (AdaptiveCircuit.krausList (injectionGadget θ)).map
        (fun K => K.mulVec (vec2 ψ (resourceVec θ))) =
      [((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • vec2 ((rot θ).mulVec ψ) (basisVec false),
       (Complex.exp ((θ : ℂ) * Complex.I) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) •
         vec2 ((rot θ).mulVec ψ) (basisVec true)] := by sorry

end ConstOverheadCompile.Main
