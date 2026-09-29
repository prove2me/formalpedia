-- Prove2me | Theorems.Thm_FeinbergLiang_ACOE_acoe_of_assumptionEC
-- name    : FeinbergLiang.ACOE.acoe_of_assumptionEC
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:02:36.806442+00:00
-- url     : https://prove2.me/theorems/d65c7b62-5cd6-4439-bc38-c6eb7c3a692a
-- title:
--   Theorem 3.2 — Assumptions W*, B and EC imply the average-cost optimality equation
-- statement:
--   Let $\mathbb X$ and $\mathbb A$ be Borel subsets of Polish spaces, and consider an MDP satisfying Assumptions W* and B. Let $\{\alpha_n\uparrow1\}$ be a sequence of nonnegative discount factors for which Assumption EC holds. Then the following hold.
--
--   1. There is a subsequence $\{\alpha_{n_k}\}$ such that $u_{\alpha_{n_k}}(x)\to\tilde u(x)$ for every $x$, uniformly on each compact subset of $\mathbb X$. Here $\tilde u$ is defined in (2.5) for the subsequence. Moreover, $\tilde u$ is finite and continuous.
--   2. With this $\tilde u$ and $w=\underline w$ (which is finite), there is a stationary policy $\phi$ satisfying the average-cost optimality equation (ACOE)
--   $$w+\tilde u(x)=c(x,\phi(x))+\int_{\mathbb X}\tilde u(y)\,q(dy\mid x,\phi(x))=\min_{a\in\mathbb A}\Big[c(x,a)+\int_{\mathbb X}\tilde u(y)\,q(dy\mid x,a)\Big],\qquad x\in\mathbb X.$$
--   3. Every stationary policy satisfying the left equation of the ACOE is average-cost optimal.
--
--   This is the paper's general sufficient condition for the ACOE under weakly continuous transition probabilities. It extends Hernández-Lerma and Lasserre (1996, Theorem 5.5.4) from setwise continuous transitions.
--
--   **Formalization Note.** Spaces are separable metric spaces whose Borel σ-algebra is standard Borel, which up to homeomorphism is the same as Borel subsets of Polish spaces. The ACOE is stated after subtracting the real lower bound of the cost from both sides, so every term lies in $[0,\infty]$. The paper writes "$=\min$"; this is read as an equality at $a=\phi(x)$ together with the inequality $\le$ for every $a\in\mathbb A$. Uniform convergence on compacts and continuity refer to the real values of $u_{\alpha_{n_k}}$ and $\tilde u$, and their finiteness is part of the conclusion. The subsequence is the strictly increasing map $\psi$ with $\alpha_{n_k}=\alpha_{\psi(k)}$.
-- source:
--   Feinberg and Liang, On the optimality equation for average cost Markov decision processes and its validity for inventory control, Annals of Operations Research 317, 2022, pp. 573-574, Theorem 3.2, Eq. (3.3)

import Mathlib
import Definitions.Def_FeinbergLiang_ACOE_MDP
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal

namespace FeinbergLiang.ACOE

/-- Theorem 3.2 (Feinberg–Liang 2022, pp. 573–574): under Assumptions W* and B, if Assumption EC
holds for a sequence of nonnegative discount factors `α_n ↑ 1`, then along some subsequence
`α_{n_k}` the relative value functions converge (pointwise, and uniformly on compact sets) to the
continuous finite function `ũ` of (2.5) for that subsequence, and a stationary policy satisfies
the ACOE (3.3); every stationary policy satisfying (3.3) is average-cost optimal. All costs are
stated after subtracting the real lower bound `M.lower` from both sides of (3.3). -/
theorem acoe_of_assumptionEC {X A : Type*} [MetricSpace X] [SeparableSpace X] [MeasurableSpace X]
    [BorelSpace X] [StandardBorelSpace X] [MetricSpace A] [SeparableSpace A] [MeasurableSpace A]
    [BorelSpace A] [StandardBorelSpace A]
    (M : MDP X A) (hW : AssumptionWStar M) (hB : AssumptionB M)
    (α : ℕ → ℝ) (hα : IsDiscountSeq α) (hEC : AssumptionEC M α) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      let ũ := uTilde M (α ∘ ψ)
      -- (i)
      (∀ x, ũ x ≠ ⊤) ∧
      (∀ x, Tendsto (fun k => uRel M (α (ψ k)) x) atTop (𝓝 (ũ x))) ∧
      (∀ C : Set X, IsCompact C →
        TendstoUniformlyOn (fun k x => (uRel M (α (ψ k)) x).toReal) (fun x => (ũ x).toReal)
          atTop C) ∧
      Continuous (fun x => (ũ x).toReal) ∧
      -- (ii)
      wLower M ≠ ⊤ ∧
      (∃ φ : X → A, Measurable φ ∧ ∀ x,
        wLower M + ũ x = M.cost x (φ x) + ∫⁻ y, ũ y ∂(M.q (x, φ x)) ∧
        ∀ a : A, wLower M + ũ x ≤ M.cost x a + ∫⁻ y, ũ y ∂(M.q (x, a))) ∧
      ∀ (φ : X → A) (hφ : Measurable φ),
        (∀ x, wLower M + ũ x = M.cost x (φ x) + ∫⁻ y, ũ y ∂(M.q (x, φ x))) →
        IsAvgOptimal M (Policy.ofStationary φ hφ) := by sorry

end FeinbergLiang.ACOE
