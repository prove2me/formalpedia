-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_fluid_limit_of_finite_cost
-- name    : BellWilliams2001.ThresholdPolicy.fluid_limit_of_finite_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:15:29.664336+00:00
-- url     : https://prove2.me/theorems/6f1693aa-46b2-4257-9fbc-c097bc31572f
-- title:
--   Lemma 9.3 — fluid limits along a cost-minimizing subsequence
-- statement:
--   Let $T=\{T^r\}$ be any sequence of scheduling control policies with
--   $$\underline J(T)=\liminf_{r\to\infty}\hat J^r(T^r)<\infty,$$
--   and let $\{r'\}$ be a subsequence along which $\hat J^{r'}(T^{r'})\to\underline J(T)$. Then, as $r'\to\infty$,
--   $$(\bar Q^{r'},\bar A^{r'},\bar S^{r'},\bar T^{r'},\bar I^{r'})\Longrightarrow(\mathbf 0,\lambda(\cdot),\mu(\cdot),\bar T^*(\cdot),\mathbf 0),$$
--   where $\lambda(t)=\lambda t$, $\mu(t)=\mu t$ and $\bar T^*$ is the fluid allocation (29).
--
--   When looking for asymptotically optimal policies one may therefore restrict to policies whose fluid-scaled allocations converge to $\bar T^*$; this is the first step of the lower bound in Theorem 5.3.
--
--   **Formalization Note** The subsequence is a strictly increasing map $\varphi:\mathbb N\to\mathbb N$. The limit is deterministic, so weak convergence is u.o.c. convergence in probability (p. 633), stated separately for each of the five blocks, which is equivalent to the joint statement for the sum norm. Admissibility is required of every $T^r$.
-- source:
--   Bell and Williams, Dynamic scheduling of a system with two parallel servers in heavy traffic with resource pooling, Ann. Appl. Probab. 11 (2001), p. 637, Lemma 9.3, (129)–(130); p. 636, (122)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Model

open Filter Topology
open scoped ENNReal

namespace BellWilliams2001.ThresholdPolicy

/-- Lemma 9.3 (p. 637). Let `T = {T^r}` be any sequence of scheduling control policies with
`J̲(T) = liminf_r Ĵ^r(T^r) < ∞` (122), and let `r'` (here `φ`, strictly increasing) be a
subsequence along which `Ĵ^{r'}(T^{r'}) → J̲(T)` (129). Then along `r'`
`(Q̄, Ā, S̄, T̄, Ī) ⟹ (0, λ(·), μ(·), T̄*(·), 0)` (130), with `λ(t) = λt`, `μ(t) = μt` and
`T̄*` of (29). The limit is deterministic, so this is u.o.c. convergence in probability
(p. 633), stated block by block (equivalent to the joint statement for the sum norm). -/
theorem fluid_limit_of_finite_cost {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (T : ℕ → Allocation Ω) (hT : ∀ n, M.IsAdmissible n (T n))
    (hfin : liminf (fun n => M.cost n (T n)) atTop < ⊤)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (fun n => M.cost (φ n) (T (φ n))) atTop
      (𝓝 (liminf (fun n => M.cost n (T n)) atTop))) :
    UocInProb M.P (fun n ω t => M.Qbar (φ n) (T (φ n)) ω t) (fun _ => 0) ∧
    UocInProb M.P (fun n ω t => M.Abar (φ n) ω t) (fun t k => M.lam k * t) ∧
    UocInProb M.P (fun n ω t => M.Sbar (φ n) ω t) (fun t j => M.mu j * t) ∧
    UocInProb M.P (fun n ω t => M.Tbar (φ n) (T (φ n)) ω t) M.fluidAllocation ∧
    UocInProb M.P (fun n ω t => M.Ibar (φ n) (T (φ n)) ω t) (fun _ => 0) := by sorry

end BellWilliams2001.ThresholdPolicy
