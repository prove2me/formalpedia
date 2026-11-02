-- Prove2me | Theorems.Thm_AllocationIndices_Freezing_eps_index_star_value_first_stage
-- name    : AllocationIndices.Freezing.eps_index_star_value_first_stage
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-01T15:07:04.455582+00:00
-- url     : https://prove2.me/theorems/c6a0f2cf-4a36-4685-8233-2e980c285ff3
-- title:
--   An ε-index* policy's value splits at the end of its first stage, and it remains ε-index*
-- statement:
--   Let $\mathcal F$ be a simple family of $k$ alternative bandit processes sharing a countable state space $T$, a transition kernel $P$, a bounded reward $r$ and a discount factor $0<a<1$. Let $h$ be an $\varepsilon$-index* policy, i.e. a policy that follows a staged rule: at the start of each stage, on the basis of the history so far, it chooses a bandit $B$ and a positive stopping time $\tau$ of $B$'s own evolution with $\nu_\tau(B)\ge\max_j\nu(B_j)-\varepsilon$, continues $B$ up to $\tau$, and then repeats the procedure.
--
--   Start the family in the state-vector $x$, and let $B_i$ and $\tau$ be the bandit and the stopping time chosen for the first stage. Then the expected total discounted reward of $h$ splits at the end of the first stage:
--   $$R_h(\mathcal F,x)\;=\;R_\tau(B_i,x_i)\;+\;E\big[a^{\tau}\,R_{h'}(\mathcal F,x^{(\tau)})\big],$$
--   where $R_\tau(B_i,x_i)=E\sum_{t<\tau}a^t r(x_i(t))$ is the expected discounted reward of the first stage, $x^{(\tau)}$ is $x$ with the state of $B_i$ replaced by $x_i(\tau)$, $a^\infty=0$, and $h'$ — the policy that $h$ follows after the first stage, which depends on the realized trajectory of $B_i$ during the stage — is again an $\varepsilon$-index* policy.
--
--   This is the regeneration property of $\varepsilon$-index* policies ("and then repeats the procedure forever", pp. 111–112): after a stage is completed, the policy is again an $\varepsilon$-index* policy started from the new state-vector. Together with the stage inequality for $R(\mathcal F,\cdot)$ it gives Corollary 4.16 by accumulating the per-stage losses $\varepsilon W_\tau$.
--
--   **Formalization Note** The staged rule is the published `StageRule` with the `IsEpsIndexStar` condition, and the policy $\pi$ continues the prescribed bandit with probability one after every history. The first stage uses `ρ.arm 0` and `ρ.stop 0` at the initial state-vector. The continuation policy is supplied as a family `π' ω` indexed by the trajectory `ω` of $B_i$ (only its part up to $\tau$ matters); each `π' ω` is required to be an $\varepsilon$-index* policy, and the integrand is required to be integrable, so that the displayed expectation is a genuine Bochner integral. On $\{\tau=\infty\}$ the factor `discountPow a ⊤ = 0` kills the term.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §4.10 pp. 111–112 (definition of ε-index* policies: 'continues B up to τ, and then repeats the procedure'), used in Corollary 4.16 p. 112

import Definitions.Def_AllocationIndices_Freezing_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices.Freezing

theorem eps_index_star_value_first_stage {T : Type*} [MeasurableSpace T] [Countable T]
    [MeasurableSingletonClass T] (P : Kernel T T) [IsMarkovKernel P] {r : T → ℝ}
    (hr : BoundedReward r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ε : ℝ} {k : ℕ}
    (ρ : StageRule k T) (hρ : ρ.IsEpsIndexStar P r a ε) (π : MarkovBanditPolicy k T)
    (hπ : ∀ (n : ℕ) (h : MarkovBanditHistory k T n), (π.select n) h {ρ.prescribedArm h} = 1)
    (x : Fin k → T) :
    ∃ π' : (ℕ → T) → MarkovBanditPolicy k T,
      (∀ ω, IsEpsIndexStarPolicy P r a ε (π' ω)) ∧
      Integrable (fun ω ↦ discountPow a (ρ.stop 0 (fun _ ↦ x) ω) *
          markovBanditDiscountedValue P r a (π' ω)
            (Function.update x (ρ.arm 0 (fun _ ↦ x)) (ω (ρ.stop 0 (fun _ ↦ x) ω).toNat)))
        (markovChainMeasure P (x (ρ.arm 0 (fun _ ↦ x)))) ∧
      markovBanditDiscountedValue P r a π x =
        stoppedReward P r a (ρ.stop 0 (fun _ ↦ x)) (x (ρ.arm 0 (fun _ ↦ x))) +
          ∫ ω, discountPow a (ρ.stop 0 (fun _ ↦ x) ω) *
              markovBanditDiscountedValue P r a (π' ω)
                (Function.update x (ρ.arm 0 (fun _ ↦ x)) (ω (ρ.stop 0 (fun _ ↦ x) ω).toNat))
            ∂markovChainMeasure P (x (ρ.arm 0 (fun _ ↦ x))) := by sorry

end AllocationIndices.Freezing
