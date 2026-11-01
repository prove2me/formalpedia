-- Prove2me | Theorems.Thm_ChenMaxEnt_maxEnt_groundSpace
-- name    : ChenMaxEnt.maxEnt_groundSpace
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:23:19.54698+00:00
-- url     : https://prove2.me/theorems/8fd3e1fb-a034-4e3b-b35b-808c866e09d2
-- title:
--   Observation 3, first bullet — the maximally mixed state on the ground space is its own inference
-- statement:
--   Let $F = (F_1,\dots,F_r)$ be Hermitian observables on $\mathcal H = \mathbb C^n$, let $c \in \mathbb R^r$, and let $V_0$ be the ground space of the Hamiltonian
--
--   $$
--   H_0 = \sum_{i=1}^r c_i F_i ,
--   $$
--
--   of dimension $m = \dim V_0 \ge 1$. Let $\rho_{V_0} = P_{V_0}/m$ be the maximally mixed state supported on $V_0$ and $\alpha_i = \operatorname{tr}(\rho_{V_0} F_i)$ its measurement results. Then the maximum entropy inference at $\alpha$ is $\rho_{V_0}$ itself:
--
--   $$
--   \rho^*(\alpha) = \frac{1}{m} P_{V_0} .
--   $$
--
--   This is what the first bullet of Observation 3 takes for granted when it calls the maximally mixed state on $V_0$ "$\rho^*$": it is the value of the inference at the point $\alpha$ where the discontinuity occurs. With $m = 1$ it says that a unique ground state is its own inference.
--
--   Differences from the source:
--   - reading: "the maximally mixed state supported on V0 be ρ∗, which corresponds to measurement results αi = tr(ρ∗Fi)" → the assertion $\rho^*(\alpha) = P_{V_0}/m$ for the inference `maxEntInference`; reason: the bullet names the maximally mixed state $\rho^*$, the symbol of the inference, and the conclusion "ρ∗(α) is discontinuous at α" uses it as the inference's value at $\alpha$.
--   - generalization: $V_0$ "degenerate" ($m > 1$) → every $m = \dim V_0 \ge 1$; reason: contains the bullet's case $m > 1$; the case $m = 1$ is used for the perturbed Hamiltonians in the proof of Observation 3.
--   - encoding: ground state space, $\operatorname{tr}(\rho F_i)$, $S$ → eigenspace of the minimum eigenvalue (`groundSpace`), real parts of traces, `QAlgorithms.vnEntropy` (base 2), $c_i$ real cast to $\mathbb C$; reason: Lean convention; same objects.
-- source:
--   Chen et al., Discontinuity of Maximum Entropy Inference and Quantum Phase Transitions, arXiv:1406.5046v2, §5.3, Observation 3, first bullet, p.22

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

/-- Chen et al., arXiv:1406.5046v2, Observation 3, first bullet, p.22: "the ground state space V0
of some Hamiltonian H0 = Σ_{i=1}^r ciFi is degenerate with the maximally mixed state supported on
V0 be ρ∗, which corresponds to measurement results αi = tr(ρ∗Fi)". If `V₀` is the ground space of
`H₀ = Σ_i c_i F_i` (real `c_i`) and `α` is the data of the maximally mixed state `P_{V₀}/m`
on `V₀`, then the maximum entropy inference at `α` is that maximally mixed state.

**Formalization Note.** Stated for every degeneracy `m = dim V₀ ≥ 1` (the bullet has `m > 1`;
the case `m = 1`, a unique ground state, is used for the perturbed Hamiltonians in the proof of
Observation 3). The ground space is the eigenspace of the minimum eigenvalue
(`groundSpace`), `P_{V₀}/m` is `maximallyMixedOn`, data are real parts of traces, `ρ*` is
`maxEntInference` (`QAlgorithms.vnEntropy`, base 2). -/
theorem maxEnt_groundSpace {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    (F : ι → Matrix n n ℂ) (hF : ∀ i, (F i).IsHermitian) (c : ι → ℝ)
    (hpos : 0 < Module.finrank ℂ (groundSpace (∑ i, (c i : ℂ) • F i))) :
    maxEntInference F (expectations F (maximallyMixedOn (groundSpace (∑ i, (c i : ℂ) • F i)))) =
      maximallyMixedOn (groundSpace (∑ i, (c i : ℂ) • F i)) := by sorry

end ChenMaxEnt
