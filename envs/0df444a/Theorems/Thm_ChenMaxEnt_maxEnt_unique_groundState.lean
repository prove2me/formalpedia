-- Prove2me | Theorems.Thm_ChenMaxEnt_maxEnt_unique_groundState
-- name    : ChenMaxEnt.maxEnt_unique_groundState
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:23:40.691953+00:00
-- url     : https://prove2.me/theorems/b3ff46d2-a7c1-4e35-86f3-1f9142ab131a
-- title:
--   Example 4 — a unique ground state is its own maximum entropy inference
-- statement:
--   Let $F = (F_1,\dots,F_r)$ be Hermitian observables on $\mathcal H = \mathbb C^n$, let $\theta \in \mathbb R^r$, and suppose the Hamiltonian $H = \sum_i \theta_i F_i$ has a **unique ground state** $|\varphi\rangle$ (its ground space is one-dimensional, $\|\varphi\| = 1$). Let $\alpha_i = \langle\varphi|F_i|\varphi\rangle$ be the measurement results of $|\varphi\rangle$. Then the maximum entropy inference at $\alpha$ is the pure ground state:
--
--   $$
--   \rho^*(\alpha) = |\varphi\rangle\langle\varphi| .
--   $$
--
--   In Example 4 the paper says this for the three-qubit Hamiltonian $H + \epsilon\sum_i X_i$ and its 2-RDMs ("ρ∗ is pure and coincide with the ground state for all ϵ ≠ 0"), and the proof of Observation 3 uses it for the perturbed Hamiltonians $H_0 + \sum_i \epsilon_i F_i$.
--
--   Differences from the source:
--   - generalization: the 2-local three-qubit Hamiltonian $H + \epsilon\sum_{i=1}^3 X_i$ and its 2-RDMs → any finite family of Hermitian observables $F$, any real $\theta$ with a unique ground state, data $\operatorname{tr}(\rho F_i)$; reason: Example 4 is the case where $F$ spans the 2-local operators (whose data are equivalent to the 2-RDMs) and $H$ is the perturbed Hamiltonian.
--   - encoding: "ρ∗ is pure and coincide with the ground state" → `maxEntInference F α = pureDensity φ` for a unit vector $\varphi$ of the one-dimensional ground space; ground space = eigenspace of the minimum eigenvalue; real parts of traces; entropy base 2; reason: Lean convention; same objects.
-- source:
--   Chen et al., Discontinuity of Maximum Entropy Inference and Quantum Phase Transitions, arXiv:1406.5046v2, Example 4, p.11

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_ChenMaxEnt_expectations
import Definitions.Def_ChenMaxEnt_jointRange
import Definitions.Def_ChenMaxEnt_linearFamily
import Definitions.Def_ChenMaxEnt_maxEntInference
import Definitions.Def_ChenMaxEnt_groundEnergy
import Definitions.Def_ChenMaxEnt_groundSpace
import Definitions.Def_ChenMaxEnt_maximallyMixedOn

open QAlgorithms Filter Topology

namespace ChenMaxEnt

/-- Chen et al., arXiv:1406.5046v2, Example 4, p.11: "As the ground state is unique when ϵ ≠ 0 and
the Hamiltonian is 2-local, the 2-RDMs of the ground state determines the state. This means that
ρ∗ is pure and coincide with the ground state for all ϵ ≠ 0." In general form: if a Hamiltonian
`H = Σ_i θ_i F_i` (real `θ_i`) in the span of the observables has a unique ground state `φ`
(a one-dimensional ground space), then the maximum entropy inference at the data of `φ` is the
pure state `|φ⟩⟨φ|`.

**Formalization Note.** The example's 2-local Hamiltonian and 2-RDMs on three qubits are replaced
by an arbitrary finite family of Hermitian observables and its data; Example 4 is the case where
`F` spans the 2-local operators, whose data are the 2-RDMs. `|φ⟩⟨φ|` is the published
`QAlgorithms.pureDensity φ`; `φ` is a unit vector of the ground space (`groundSpace`, the
eigenspace of the minimum eigenvalue), which has `finrank = 1`. -/
theorem maxEnt_unique_groundState {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    (F : ι → Matrix n n ℂ) (hF : ∀ i, (F i).IsHermitian) (θ : ι → ℝ)
    (huniq : Module.finrank ℂ (groundSpace (∑ i, (θ i : ℂ) • F i)) = 1)
    (φ : EuclideanSpace ℂ n) (hφ : ‖φ‖ = 1) (hφmem : φ ∈ groundSpace (∑ i, (θ i : ℂ) • F i)) :
    maxEntInference F (expectations F (pureDensity φ)) = pureDensity φ := by sorry

end ChenMaxEnt
