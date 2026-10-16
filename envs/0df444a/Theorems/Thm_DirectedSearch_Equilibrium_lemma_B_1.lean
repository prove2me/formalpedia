-- Prove2me | Theorems.Thm_DirectedSearch_Equilibrium_lemma_B_1
-- name    : DirectedSearch.Equilibrium.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:01:01.449055+00:00
-- url     : https://prove2.me/theorems/afce1193-da15-482d-8ca2-83a30c97f2d3
-- title:
--   Lemma B.1, p. 40 — ρ = max_{τ≥0} B(τ) is a fixed point of B, and B is unimodal around it
-- statement:
--   Let $\delta>0$, and let finitely many opposite types $i$ have meeting rates $\lambda_i>0$, thresholds $\tau_i\ge 0$, and atomless probability laws $F_i$ on $\mathbb R$ with finite mean. Define
--   $$B(\tau)=\frac{\sum_{i}\lambda_i\int_{\max(\tau,\tau_i)}^\infty u\,dF_i}{\delta+\sum_{i}\lambda_i\int_{\max(\tau,\tau_i)}^\infty dF_i},\qquad \rho=\sup_{\tau\ge 0}B(\tau).$$
--   Then:
--   1. the supremum is attained: $\rho=\max_{\tau\ge0}B(\tau)$;
--   2. $B(\rho)=\rho$;
--   3. $B$ is (weakly) increasing on $(-\infty,\rho]$;
--   4. $B$ is (weakly) decreasing on $[\rho,\infty)$.
--
--   This is the generalization of Lemma 4.5 to nonzero opposite thresholds and several opposite types: a type's expected utility, as a function of its own threshold, is unimodal and peaks exactly at its own fixed point.
--
--   **Formalization Note.** The page says "Let ρ satisfies the fixed point equation ρ = max B"; ρ is read as the maximum and $B(\rho)=\rho$ is the conclusion. "Monotonically increasing/decreasing" is weak monotonicity (strictness fails where the $F_i$ put no mass). The finite-mean hypothesis is implicit in the paper and stated explicitly; without it the tail integrals would be meaningless. The index set may be empty, in which case $B\equiv0$.
-- source:
--   Immorlica, Lucier, Manshadi, Wei, Designing Approximately Optimal Search on Matching Platforms, arXiv:2102.09017v2, p. 40, Lemma B.1

import Mathlib
import Definitions.Def_DirectedSearch_Equilibrium_Setting

namespace DirectedSearch.Equilibrium
open MeasureTheory
theorem lemma_B_1 {ι : Type} [Fintype ι] (δ : ℝ) (lam τ' : ι → ℝ) (F : ι → Measure ℝ)
    (hδ : 0 < δ) (hlam : ∀ i, 0 < lam i) (hτ' : ∀ i, 0 ≤ τ' i)
    (hprob : ∀ i, IsProbabilityMeasure (F i)) (hatom : ∀ i, NullSingletonClass (F i))
    (hint : ∀ i, Integrable id (F i)) :
    IsGreatest (ownU δ lam τ' F '' Set.Ici 0) (ownRho δ lam τ' F) ∧
      ownU δ lam τ' F (ownRho δ lam τ' F) = ownRho δ lam τ' F ∧
      MonotoneOn (ownU δ lam τ' F) (Set.Iic (ownRho δ lam τ' F)) ∧
      AntitoneOn (ownU δ lam τ' F) (Set.Ici (ownRho δ lam τ' F)) := by sorry
end DirectedSearch.Equilibrium
