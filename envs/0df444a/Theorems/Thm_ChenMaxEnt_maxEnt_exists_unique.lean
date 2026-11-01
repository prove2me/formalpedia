-- Prove2me | Theorems.Thm_ChenMaxEnt_maxEnt_exists_unique
-- name    : ChenMaxEnt.maxEnt_exists_unique
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:23:26.340601+00:00
-- url     : https://prove2.me/theorems/5eb55501-e453-4eec-a622-971c811d032e
-- title:
--   Eq. (2) — existence and uniqueness of the maximum entropy inference
-- statement:
--   Let $\mathcal H = \mathbb C^n$, let $F = (F_1,\dots,F_r)$ be Hermitian observables on $\mathcal H$, and let $\alpha \in D_F$ be an attainable vector of measurement results. Then the linear family
--
--   $$
--   L(\alpha) = \{\rho \in \mathcal D \mid \operatorname{tr}(\rho F_i) = \alpha_i,\ i = 1,\dots,r\}
--   $$
--
--   contains **exactly one** state $\rho^*$ of maximal von Neumann entropy:
--
--   $$
--   \exists!\, \rho^* \in L(\alpha) \quad\text{with}\quad S(\sigma) \le S(\rho^*) \ \text{ for all } \sigma \in L(\alpha).
--   $$
--
--   This is the statement that makes the maximum entropy inference $\rho^*(\alpha) = \operatorname{argmax}_{\rho\in L(\alpha)} S(\rho)$ well defined on $D_F$. The paper calls it well known and cites the principle of maximum entropy (Jaynes; Wichmann); it gives no proof.
--
--   Differences from the source:
--   - encoding: "for any given measurement results α" → `α ∈ jointRange F` ($D_F$); reason: measurement results are points of $D_F$ (p.4, "Given any measurement result α ∈ DF"); for $\alpha \notin D_F$ the family $L(\alpha)$ is empty and (2) is undefined.
--   - encoding: d-dimensional Hilbert space, observables $F_1,\dots,F_r$, $\operatorname{tr}(\rho F_i)$ and $S$ with unspecified logarithm → $\mathbb C^n$ for a finite index type, Hermitian matrices indexed by a finite type, real parts of traces, `QAlgorithms.vnEntropy` (base 2); reason: Lean convention; the traces are real for states and Hermitian $F_i$, and the base of the logarithm does not change a maximizer.
-- source:
--   Chen et al., Discontinuity of Maximum Entropy Inference and Quantum Phase Transitions, arXiv:1406.5046v2, eq. (2), p.5

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
arXiv:1406.5046v2, eq. (2), p.5: "That is, for any given measurement results α, there is a
unique state ρ∗ ∈ L(α), given by ρ∗(α) = argmax_{ρ ∈ L(α)} S(ρ), (2) where S(ρ) is the von
Neumann entropy of ρ." For every attainable data point `α ∈ D_F` the linear family `L(α)` has
exactly one state of maximal von Neumann entropy.

**Formalization Note.** `n` is a finite index type (`H = ℂ^n`), the observables are Hermitian
matrices `F i`, data are real parts of traces (`expectations`), states are density matrices,
`S` is `QAlgorithms.vnEntropy` (base 2; the base does not change the maximizer). "Measurement
results" are points of `D_F` (`jointRange F`), since `L(α)` is empty otherwise. -/
theorem maxEnt_exists_unique {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    (F : ι → Matrix n n ℂ) (hF : ∀ i, (F i).IsHermitian) (α : ι → ℝ) (hα : α ∈ jointRange F) :
    ∃! ρ, ρ ∈ linearFamily F α ∧ ∀ σ ∈ linearFamily F α, vnEntropy σ ≤ vnEntropy ρ := by sorry

end ChenMaxEnt
