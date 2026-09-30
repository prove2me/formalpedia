-- Prove2me | Theorems.Thm_AllocationIndices_interchange_portions
-- name    : AllocationIndices.interchange_portions
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T02:32:04.153227+00:00
-- url     : https://prove2.me/theorems/48cf59e3-9fe5-46a6-a9b7-9469ecf542e3
-- title:
--   Lemma 2.4: with ν(B₁) > ν(B₂) and τ attaining ν(B₁), continuing B₁ for τ then B₂ for σ beats the reverse order
-- statement:
--   **Lemma 2.4.** If bandit processes $B_1$ and $B_2$ have indices $\nu(B_1)$ and $\nu(B_2)$ with $\nu(B_1) > \nu(B_2)$, and $\tau$ is a stopping time for $B_1$ such that $\nu_\tau(B_1) = \nu(B_1)$, while $\sigma$ is an arbitrary stopping time for $B_2$, then the expected reward from selecting $B_1$ for time $\tau$, and then $B_2$ for time $\sigma$, is greater than from reversing the order of selection.
--
--   Formally: $B_1, B_2$ bandit processes on countable state spaces $S_1, S_2$ with bounded rewards, the same discount factor $a \in (0,1)$, initial states $x_1, x_2$ with $\nu(B_2, x_2) < \nu(B_1, x_1)$; $\tau$ a positive stopping time of $B_1$ with $R_\tau(B_1)/W_\tau(B_1) = \nu(B_1, x_1)$; $\sigma$ any positive stopping time of $B_2$. Then
--   $$R_\sigma(B_2) + \mathbb{E}[a^\sigma]\, R_\tau(B_1) < R_\tau(B_1) + \mathbb{E}[a^\tau]\, R_\sigma(B_2),$$
--   the two sides being the expected rewards of the two orders, since the processes are independent.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §2.7 p. 34, Lemma 2.4 with its proof

import Definitions.Def_AllocationIndices_Index

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices

theorem interchange_portions {S₁ S₂ : Type*} [MeasurableSpace S₁] [Countable S₁]
    [MeasurableSingletonClass S₁] [MeasurableSpace S₂] [Countable S₂] [MeasurableSingletonClass S₂]
    (P₁ : Kernel S₁ S₁) [IsMarkovKernel P₁] {r₁ : S₁ → ℝ} (hr₁ : BoundedReward r₁)
    (P₂ : Kernel S₂ S₂) [IsMarkovKernel P₂] {r₂ : S₂ → ℝ} (hr₂ : BoundedReward r₂)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {x₁ : S₁} {x₂ : S₂}
    (hν : gittinsIndex P₂ r₂ a x₂ < gittinsIndex P₁ r₁ a x₁)
    {τ : (ℕ → S₁) → ℕ∞} (hτ : IsPositiveStoppingTime τ)
    (hτν : stoppedRatio P₁ r₁ a τ x₁ = gittinsIndex P₁ r₁ a x₁)
    {σ : (ℕ → S₂) → ℕ∞} (hσ : IsPositiveStoppingTime σ) :
    interchangeValue P₂ r₂ P₁ r₁ a σ τ x₂ x₁ < interchangeValue P₁ r₁ P₂ r₂ a τ σ x₁ x₂ := by sorry

end AllocationIndices
