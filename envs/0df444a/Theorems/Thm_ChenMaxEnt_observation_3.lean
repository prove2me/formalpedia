-- Prove2me | Theorems.Thm_ChenMaxEnt_observation_3
-- name    : ChenMaxEnt.observation_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:23:27.319228+00:00
-- url     : https://prove2.me/theorems/ae555be9-7d53-4b36-bf9e-e067df9e66e1
-- title:
--   Observation 3 — sufficient condition for the discontinuity of the maximum entropy inference
-- statement:
--   Let $\mathcal H = \mathbb C^n$ and let $F = (F_1,\dots,F_r)$ be Hermitian observables on $\mathcal H$. Suppose:
--
--   1. the ground space $V_0$ of some Hamiltonian $H_0 = \sum_{i=1}^r c_i F_i$ ($c \in \mathbb R^r$) is **degenerate**, of dimension $m > 1$; let $\rho^* = P_{V_0}/m$ be the maximally mixed state supported on $V_0$ and $\alpha_i = \operatorname{tr}(\rho^* F_i)$ its measurement results;
--   2. there is an orthonormal basis $|\psi_1\rangle,\dots,|\psi_m\rangle$ of $V_0$ satisfying the partial error-detecting condition
--   $$
--   \langle\psi_a|F_i|\psi_b\rangle = 0 \qquad \text{for all } a \ne b \text{ and all } i; \tag{31}
--   $$
--   3. there is a sequence $\epsilon^{(k)} \in \mathbb R^r$ with $\epsilon^{(k)} \to 0$ such that every Hamiltonian $H_0 + \sum_i \epsilon^{(k)}_i F_i$ has a unique ground state $|\psi(\epsilon^{(k)})\rangle$ (a unit vector spanning its one-dimensional ground space), and
--   $$
--   \lim_{k\to\infty} |\psi(\epsilon^{(k)})\rangle = |\psi\rangle := \frac{1}{\sqrt m}\sum_{a=1}^m |\psi_a\rangle. \tag{33}
--   $$
--
--   Then the maximum entropy inference $\rho^*(\cdot)$ is **discontinuous at the point $\alpha$**, as a function on the set $D_F$ of attainable measurement results.
--
--   The hypotheses describe a level crossing that the measured observables cannot see: the degenerate ground space $V_0$ contains the pure state $|\psi\rangle$ with the same data as the mixed state $P_{V_0}/m$, and the perturbed ground states approach it. The paper's Example 6 (p.22) is an instance in dimension 3.
--
--   Differences from the source:
--   - reading: "there exists a basis |ψa⟩ of V0" → an orthonormal family $(\psi_a)_{a \in \mathrm{Fin}\, m}$ of vectors of $V_0$, with $\dim V_0 = m$ (hence an orthonormal basis); reason: $|\psi\rangle$ is the limit (33) of unit vectors and so a unit vector, which fails for a generic non-orthogonal basis ($\psi_1 = e_0$, $\psi_2 = (e_0+e_1)/\sqrt2$ gives $\||\psi\rangle\|^2 = 1 + 1/\sqrt2$, making the hypotheses unsatisfiable); (31) is the Knill–Laflamme error-detecting condition, stated for orthonormal bases.
--   - encoding: $\langle\psi_a|F_i|\psi_b\rangle = \delta_{ab}$ for $a \ne b$ → $= 0$; reason: $\delta_{ab} = 0$ for $a \ne b$.
--   - generalization: "has unique ground states |ψ(ϵ)⟩ at any nonzero ϵ" → a unique ground state at every term $\epsilon^{(k)}$ of the sequence; reason: a weaker hypothesis, implied by the paper's; it forces $\epsilon^{(k)} \ne 0$ because $\dim V_0 > 1$.
--   - encoding: the ground states $|\psi(\epsilon)\rangle$ and the limit (33) → unit vectors $\varphi_k$ in the one-dimensional ground spaces with $\varphi_k \to |\psi\rangle$ along the sequence; reason: a ground state is a unit vector of the ground space, and (33) is taken along the sequence (32).
--   - encoding: "ρ∗(α) is discontinuous at the point α" → `¬ ContinuousWithinAt (maxEntInference F) (jointRange F) α` with $\alpha$ the data of `maximallyMixedOn V₀`; reason: $\rho^*$ is a function on $D_F$ (eq. (24)); off $D_F$ the Lean value is junk.
--   - encoding: Hilbert space, observables, traces, entropy, ground space → $\mathbb C^n$ for a finite index type, Hermitian matrices indexed by a finite type, real parts of traces, `QAlgorithms.vnEntropy` (base 2), eigenspace of the minimum eigenvalue, $c$ and $\epsilon$ real cast to $\mathbb C$; reason: Lean convention; same objects.
-- source:
--   Chen et al., Discontinuity of Maximum Entropy Inference and Quantum Phase Transitions, arXiv:1406.5046v2, §5.3, Observation 3, p.22 (eqs. (31)–(33))

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

/-- Chen et al., *Discontinuity of Maximum Entropy Inference and Quantum Phase Transitions*,
arXiv:1406.5046v2, Observation 3, p.22: "For a set of observables F = (F1, . . . , Fr), if:
• the ground state space V0 of some Hamiltonian H0 = Σ_{i=1}^r ciFi is degenerate with the
maximally mixed state supported on V0 be ρ∗, which corresponds to measurement results
αi = tr(ρ∗Fi); • there exists a basis |ψa⟩ of V0 such that ⟨ψa|Fi|ψb⟩ = δab (31) for any a ≠ b
and Fi ∈ F; • there exists a sequence of ϵ = (ϵ1, . . . , ϵr) → (0, . . . , 0), (32) such that the
Hamiltonian H = H0 + Σ_{i=1}^r ϵiFi has unique ground states |ψ(ϵ)⟩ at any nonzero ϵ, and
lim_{ϵ→(0,...,0)} |ψ(ϵ)⟩ = |ψ⟩, (33) where |ψ⟩ = (1/√m) Σ_{a=1}^m |ψa⟩ and m is the ground state
degeneracy of H0 (m > 1); then ρ∗(α) is discontinuous at the point α."

**Formalization Note.** `H = ℂ^n` for a finite index type `n`; the observables are Hermitian
`F i`, `i ∈ ι` finite; `c` and `ε_k` are real (cast to `ℂ`). The ground space is the eigenspace of
the minimum eigenvalue (`groundSpace`), the degeneracy is its `finrank` (`= m > 1`), and
`ρ* = P_{V₀}/m` is `maximallyMixedOn V₀`, whose data are `α` (real parts of traces). The basis
`(ψ_a)_{a ∈ Fin m}` is read as orthonormal (the limit of unit vectors in (33) must be a unit
vector), lying in `V₀`; with `finrank V₀ = m` it is a basis of `V₀`. Condition (31) is
`⟨ψ_a|F_i|ψ_b⟩ = 0` for `a ≠ b`. The sequence `ε_k → 0` has, at every term, a one-dimensional
ground space of `H₀ + Σ_i ε_{k,i} F_i` (this forces `ε_k ≠ 0`), with a unit ground vector `φ_k`,
and `φ_k → ψ`. The conclusion is discontinuity of `ρ* = maxEntInference F` at `α` as a function on
`D_F = jointRange F`; `S` is `QAlgorithms.vnEntropy` (base 2). -/
theorem observation_3 {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    (F : ι → Matrix n n ℂ) (hF : ∀ i, (F i).IsHermitian) (c : ι → ℝ) (m : ℕ) (hm : 1 < m)
    (hdeg : Module.finrank ℂ (groundSpace (∑ i, (c i : ℂ) • F i)) = m)
    (ψb : Fin m → EuclideanSpace ℂ n) (hon : Orthonormal ℂ ψb)
    (hmem : ∀ a, ψb a ∈ groundSpace (∑ i, (c i : ℂ) • F i))
    (h31 : ∀ a b, a ≠ b → ∀ i, inner ℂ (ψb a) (Matrix.toEuclideanLin (F i) (ψb b)) = 0)
    (ε : ℕ → ι → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (huniq : ∀ k, Module.finrank ℂ (groundSpace (∑ i, ((c i + ε k i : ℝ) : ℂ) • F i)) = 1)
    (φ : ℕ → EuclideanSpace ℂ n) (hφnorm : ∀ k, ‖φ k‖ = 1)
    (hφmem : ∀ k, φ k ∈ groundSpace (∑ i, ((c i + ε k i : ℝ) : ℂ) • F i))
    (hlim : Tendsto φ atTop (𝓝 ((1 / Real.sqrt m : ℝ) • ∑ a, ψb a))) :
    ¬ ContinuousWithinAt (maxEntInference F) (jointRange F)
        (expectations F (maximallyMixedOn (groundSpace (∑ i, (c i : ℂ) • F i)))) := by sorry

end ChenMaxEnt
