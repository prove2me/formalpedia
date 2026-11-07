-- Prove2me | Theorems.Thm_BoolCSPDel_sketch_sparsify
-- name    : BoolCSPDel.sketch_sparsify
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:55:53.060206+00:00
-- url     : https://prove2.me/theorems/0aa09ecd-a180-402c-960d-e2ca374a725e
-- title:
--   §4.3 — sketches for exact sparsification need $\Omega_k(n^d)$ bits
-- statement:
--   Let $\Gamma$ be a nonempty language of nonempty proper relations, possibly constant-satisfiable, and $d=\deg_{\mathbb Z}(\Gamma)$. There is a constant $F$ such that, for all large $n$, there is a distribution on instances with frequencies at most $F$ for which every public-coin linear sketch returning an exact sparsifier with average error at most $1/3$ has size at least $cn^d$.
--
--   This is the sketching half of the lower bound for sparsification, where no pinning is needed.
--
--   **Formalization Note** The transfer to streaming used for Corollary 4.16, [JLY26, Corollary 6.1.4(3)], is described in prose only in the paper and is not posed.
--
--   Differences from the source:
--   - encoding: sketching lower bound stated in prose, with "the same INDEX reduction" → the shape of corollary_4_15, with distribution before sketch and a decoder returning a set of constraints; reason: this is what the reduction of p.29 gives
--   - encoding: average error at most 1/3 → measurable events A f inside the success sets, with Σ_f D(f) μ(A f) ≥ 2/3; reason: an inner-measure form of the average; for measurable success sets it is the same
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519…), §4.3, p.29

import Mathlib
import Definitions.Def_BoolCSPDel_degZ
import Definitions.Def_BoolCSPDel_Con
import Definitions.Def_BoolCSPDel_Sketch

open MeasureTheory

namespace BoolCSPDel

/-- **Sketching lower bound for exact sparsification.** Bandekar, Sharma, Velusamy, *A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions*, STOC 2027 submission (manuscript sha256 15f83519…), §4.3, p.29: "The same INDEX reduction
therefore gives an `Ω_k(n^d)` sketching lower bound, where `d = deg_ℤ(Γ)`."

The shape of Corollary 4.15, for a nonempty language, with no non-constant-satisfiability hypothesis
and with a decoder returning a set of constraints that must be an exact sparsifier.

**Formalization Note.** The transfer [JLY26, Corollary 6.1.4(3)] is described in prose only (p.29) and is
not posed here. -/
theorem sketch_sparsify (k : ℕ) : ∃ (c : ℝ) (F N₀ : ℕ), 0 < c ∧
    ∀ Γ : Lang k, Γ.Nonempty → AllNonemptyProper Γ → ∀ n, N₀ ≤ n →
      ∃ D : PMF (Con Γ (Fin n) → ℤ), (∀ f ∈ D.support, ∀ C, 0 ≤ f C ∧ f C ≤ F) ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (σ : Sketch (Con Γ (Fin n)) Ω (Finset (Con Γ (Fin n))))
          (A : (Con Γ (Fin n) → ℤ) → Set Ω),
          (∀ f, MeasurableSet (A f)) →
          (∀ f, A f ⊆ {ω | IsExactSparsifier (σ.out ω f) f}) →
          (2 / 3 : ENNReal) ≤ ∑' f, D f * μ (A f) →
          ∀ B : ℝ, σ.HasSize B → c * (n : ℝ) ^ degZLang Γ ≤ B := by sorry

end BoolCSPDel
