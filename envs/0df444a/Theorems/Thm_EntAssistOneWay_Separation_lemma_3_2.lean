-- Prove2me | Theorems.Thm_EntAssistOneWay_Separation_lemma_3_2
-- name    : EntAssistOneWay.Separation.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:46:17.886901+00:00
-- url     : https://prove2.me/theorems/7592d388-a41a-48c6-aa47-8508fab6047d
-- title:
--   Lemma 3.2 — exact optimal quantum success probability
-- statement:
--   Let $X,Y$ be finite input sets, $\mathrm{Dom}\subseteq X\times Y$, $f:\mathrm{Dom}\to\{0,1\}$, and let $\mu$ be a law on $\mathrm{Dom}$. For $C$ qubits and a family of binary POVMs $M$, put
--   $$V(M)=\sum_x\left\|\sum_{t\in\mathrm{Dom}:t_X=x}\mu(t)M^{t_Y}_{f(t)}\right\|_\infty.$$
--   Every unassisted strategy has success at most $V(M)$ for its measurement family. Conversely, for every such family there is a choice of Alice's message states attaining $V(M)$. In addition the optimum over all strategies is attained, so the best success probability is $\max_M V(M)$.
--
--   This is the exact characterization, including both directions and attainment, for partial functions as well as total ones.
--
--   Differences from the source:
--   - encoding: a distribution on a partial-function domain and conditional expectations → a finite domain subtype and unconditioned weighted sums inside spectral norms; reason: homogeneity of the norm absorbs each marginal mass and gives zero for zero-marginal rows without conditional division
--   - encoding: finite-dimensional coordinate Hilbert spaces and C-bit or C-qubit messages → Fin d matrix indices and message indices Fin (2^C); reason: these label every coordinate and every length-C message without restricting states or measurements
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), p. 16, Lemma 3.2

import Definitions.Def_EntAssistOneWay_Separation_OptimalSuccess

open scoped BigOperators ComplexOrder
open Classical
open BooleanHiddenPartition.LowerBounds
set_option autoImplicit false

namespace EntAssistOneWay.Separation

noncomputable section

/-- Lemma 3.2, p. 16: the universal upper bound and pointwise attainability,
with actual attainment of the global maximum as well. -/
theorem lemma_3_2 (X Y : Type) [Fintype X] [Fintype Y]
    (Dom : Finset (X × Y)) (f : Dom → Bool) (μ : FiniteLaw Dom) (C : ℕ) :
    (∀ P : QuantumStrategy X Y C,
      partialSuccess Dom f μ P ≤ povmValue Dom f μ (strategyEffect P)) ∧
    (∀ M : Y → BinaryEffect (Fin (2 ^ C)),
      ∃ P : QuantumStrategy X Y C,
        (∀ y, P.effect y = (M y).op) ∧ partialSuccess Dom f μ P = povmValue Dom f μ M) ∧
    (∃ P : QuantumStrategy X Y C, ∀ Q : QuantumStrategy X Y C,
      partialSuccess Dom f μ Q ≤ partialSuccess Dom f μ P) := by sorry

end

end EntAssistOneWay.Separation
