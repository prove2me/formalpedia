-- Prove2me | Theorems.Thm_ChenMaxEnt_discontinuous_of_seq
-- name    : ChenMaxEnt.discontinuous_of_seq
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T15:23:30.536471+00:00
-- url     : https://prove2.me/theorems/53858016-3ef3-475f-a084-718aae93ee05
-- title:
--   Eq. (24) — a sequence $\alpha_s \to \alpha$ with $\rho^*(\alpha_s) \not\to \rho^*(\alpha)$ gives a discontinuity
-- statement:
--   Let $F = (F_1,\dots,F_r)$ be Hermitian observables on $\mathcal H = \mathbb C^n$ and $\alpha \in \mathbb R^r$. Suppose there is a sequence $(\alpha_s)$ of attainable measurement results, $\alpha_s \in D_F$, with $\alpha_s \to \alpha$ but
--
--   $$
--   \rho^*(\alpha_s) \not\to \rho^*(\alpha). \tag{24}
--   $$
--
--   Then the maximum entropy inference $\rho^*$, as a function on $D_F$, is discontinuous at $\alpha$.
--
--   This fixes the paper's notion of discontinuity of $\rho^*$: the conclusion of Observation 3 is reached by exhibiting such a sequence.
--
--   Differences from the source:
--   - encoding: "there is discontinuity of ρ∗(α)" → `¬ ContinuousWithinAt (maxEntInference F) (jointRange F) α`; reason: $\rho^*$ is a function on $D_F$ (off $D_F$ the Lean value is junk), data carry the topology of $\mathbb R^r$ and states that of $\mathbb C^{n\times n}$.
--   - encoding: "a sequence αs approaching α" → a sequence of points of $D_F$ converging to $\alpha$; reason: $\rho^*(\alpha_s)$ is only defined for measurement results $\alpha_s \in D_F$.
-- source:
--   Chen et al., Discontinuity of Maximum Entropy Inference and Quantum Phase Transitions, arXiv:1406.5046v2, §5.1, eq. (24), p.19

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

/-- Chen et al., arXiv:1406.5046v2, §5.1, eq. (24), p.19: "If there is a sequence αs approaching
α but ρ∗(αs) ↛ ρ∗(α), (24) then there is discontinuity of ρ∗(α)." If a sequence of attainable
data `α_s ∈ D_F` converges to `α` while the maximum entropy inferences `ρ*(α_s)` do not converge
to `ρ*(α)`, then `ρ*` is discontinuous at `α` as a function on `D_F`.

**Formalization Note.** Discontinuity of `ρ*` is `¬ ContinuousWithinAt (maxEntInference F)
(jointRange F) α`: the inference is a map on the set `D_F` of attainable data (off `D_F` it is a
junk value). Data carry the product topology of `ℝ^ι`, matrices that of `ℂ^{n×n}`. -/
theorem discontinuous_of_seq {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
    (F : ι → Matrix n n ℂ) (hF : ∀ i, (F i).IsHermitian) (α : ι → ℝ) (αs : ℕ → ι → ℝ)
    (hαs : ∀ s, αs s ∈ jointRange F) (hlim : Tendsto αs atTop (𝓝 α))
    (hnot : ¬ Tendsto (fun s => maxEntInference F (αs s)) atTop (𝓝 (maxEntInference F α))) :
    ¬ ContinuousWithinAt (maxEntInference F) (jointRange F) α := by sorry

end ChenMaxEnt
