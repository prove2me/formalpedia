-- Prove2me | Theorems.Thm_EntAssistOneWay_Separation_theorem_1_1
-- name    : EntAssistOneWay.Separation.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:43.747344+00:00
-- url     : https://prove2.me/theorems/390cd3f1-c6c8-4f10-860a-b605a69a7a14
-- title:
--   Theorem 1.1 — exponential separation for a family of total functions
-- statement:
--   There is one family of total Boolean functions $f_n:\{0,1\}^n\times\{0,1\}^n\to\{0,1\}$, positive absolute constants $c_1,\ldots,c_5$, and $N\ge1$, such that for every $n\ge N$ all five claims hold at worst-case error at most $1/3$:
--   $$C^{1,*}_{1/3}(f_n)\le c_1\log_2n,\qquad c_2n\le E_n\le c_3n,$$
--   $$c_4n^{1/3}\le Q^{1,\mathrm{pub}}_{1/3}(f_n)\le c_5n^{1/3},\qquad c_4n^{1/3}\le C^{1,\mathrm{pub}}_{1/3}(f_n)\le c_5n^{1/3}.$$
--   The EPR-pair bounds concern the same protocol exhibiting the entanglement-assisted classical upper bound. Each lower bound quantifies over every successful protocol; each upper bound exhibits one. The family and constants precede $n$. The paper writes $O(\log n)$ and three $\Theta$ statements, retained with existential universal constants and an eventual threshold.
--
--   This is the full headline separation, with both directions of each unassisted complexity claim; the goal does not require the witness family to be named shifted equality.
--
--   Differences from the source:
--   - generalization: public coins in finite-input one-way communication → the lower bound holds for every measurable public seed on any probability space; reason: Born probabilities are bounded and measurable, so integrating the distributional lower bound covers every such seed, including the source coins
--   - encoding: O and Θ bounds for a family indexed by n → one family, five positive constants, and a common eventual threshold N; reason: finitely many eventual estimates can share a threshold and the two unassisted models can share a smaller lower and larger upper constant
--   - encoding: existence of a public-coin quantum upper-bound protocol → the upper witness uses a Borel real public seed; reason: finite public randomness is represented by a finitely supported law on distinct real values, so no source instance is removed
--   - encoding: finite-dimensional coordinate Hilbert spaces and C-bit or C-qubit messages → Fin d matrix indices and message indices Fin (2^C); reason: these label every coordinate and every length-C message without restricting states or measurements
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), p. 3, Theorem 1.1; pp. 36–37, proof

import Definitions.Def_EntAssistOneWay_Separation_Analysis
import Definitions.Def_EntAssistOneWay_Separation_Probability
import Definitions.Def_EntAssistOneWay_Separation_EAProtocol

open scoped BigOperators ComplexOrder
open Classical
open BooleanHiddenPartition.LowerBounds
set_option autoImplicit false

namespace EntAssistOneWay.Separation

noncomputable section

/-- Theorem 1.1, p. 3: one family, all five asymptotic claims. -/
theorem theorem_1_1 :
    ∃ f : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Bool,
      ∃ c₁ c₂ c₃ c₄ c₅ : ℝ,
        0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧ 0 < c₄ ∧ 0 < c₅ ∧
        ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
          (∃ (E C : ℕ) (P : EAProtocol (Fin n → Bool) (Fin n → Bool) E C),
            c₂ * n ≤ (E : ℝ) ∧ (E : ℝ) ≤ c₃ * n ∧ (C : ℝ) ≤ c₁ * log₂ n ∧
            ComputesWithError (f n) (eaAccept P) (1 / 3)) ∧
          (∀ (Ω : Type) [MeasurableSpace Ω] (C : ℕ)
            (P : QuantumProtocol (Fin n → Bool) (Fin n → Bool) Ω C),
            ComputesWithError (f n) (randomizedQuantumAccept P) (1 / 3) →
            c₄ * Real.rpow n (1 / 3) ≤ (C : ℝ)) ∧
          (∃ (C : ℕ) (P : QuantumProtocol (Fin n → Bool) (Fin n → Bool) ℝ C),
            (C : ℝ) ≤ c₅ * Real.rpow n (1 / 3) ∧
            ComputesWithError (f n) (randomizedQuantumAccept P) (1 / 3)) ∧
          (∀ (C : ℕ) (P : ClassicalProtocol (Fin n → Bool) (Fin n → Bool) C),
            ComputesWithError (f n) (classicalAccept P) (1 / 3) →
            c₄ * Real.rpow n (1 / 3) ≤ (C : ℝ)) ∧
          (∃ (C : ℕ) (P : ClassicalProtocol (Fin n → Bool) (Fin n → Bool) C),
            (C : ℝ) ≤ c₅ * Real.rpow n (1 / 3) ∧
            ComputesWithError (f n) (classicalAccept P) (1 / 3)) := by sorry

end

end EntAssistOneWay.Separation
