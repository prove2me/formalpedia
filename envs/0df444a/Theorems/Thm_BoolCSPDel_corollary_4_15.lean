-- Prove2me | Theorems.Thm_BoolCSPDel_corollary_4_15
-- name    : BoolCSPDel.corollary_4_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:55:39.476615+00:00
-- url     : https://prove2.me/theorems/67cf60d3-0156-47c7-976d-1d38da4b88f2
-- title:
--   Corollary 4.15 (first sentence) — sketches deciding $\mathrm{CSP}(\Gamma)$ need $\Omega_k(n^d)$ bits
-- statement:
--   Let $\Gamma$ be a language of nonempty proper relations, not constant-satisfiable, and $d=\deg_{\mathbb Z}(\Gamma)$. There is a constant $F$ such that, for all large $n$, there is a distribution on instances on $n$ variables with frequencies at most $F$ for which every public-coin linear sketch deciding satisfiability with average error at most $1/3$ has size at least $cn^d$.
--
--   The distribution does not depend on the sketch. This is the sketching half of the lower bound.
--
--   Differences from the source:
--   - generalization: relations of a common arity k → arity at most k, each its own; reason: p.21 uses original arities in the lower-bound constructions; Corollary 4.16 says arity at most k; a common arity is a special case
--   - encoding: F_Γ and Ω_k for a fixed Γ → c, F, N₀ chosen for k before Γ; reason: finitely many languages of arity at most k (p.17)
--   - encoding: average error at most 1/3 → measurable events A f inside the success sets, with Σ_f D(f) μ(A f) ≥ 2/3; reason: an inner-measure form of the average; for measurable success sets it is the same
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519…), Corollary 4.15, p.28

import Mathlib
import Definitions.Def_BoolCSPDel_degZ
import Definitions.Def_BoolCSPDel_Con
import Definitions.Def_BoolCSPDel_Sketch

open MeasureTheory

namespace BoolCSPDel

/-- **Corollary 4.15, first sentence (sketching lower bound).** Bandekar, Sharma, Velusamy, *A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions*, STOC 2027 submission (manuscript sha256 15f83519…), Corollary 4.15, p.28.

For a non-constant-satisfiable language of nonempty proper relations there is, for every large `n`, one
distribution on instances with frequencies at most `F` such that **every** public-coin linear sketch
deciding satisfiability with average error at most `1/3` has size `Ω_k(n^d)`.

**Formalization Note.** The distribution comes first and the sketch after it, as printed. Average error
is over the seed and the instance, with measurable events inside the success sets. Mixed arities are
allowed; `c`, `F`, `N₀` depend on `k` only, as finitely many languages have arity at most `k` (p.17). -/
theorem corollary_4_15 (k : ℕ) : ∃ (c : ℝ) (F N₀ : ℕ), 0 < c ∧
    ∀ Γ : Lang k, AllNonemptyProper Γ → ¬ ConstSat Γ → ∀ n, N₀ ≤ n →
      ∃ D : PMF (Con Γ (Fin n) → ℤ), (∀ f ∈ D.support, ∀ C, 0 ≤ f C ∧ f C ≤ F) ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (σ : Sketch (Con Γ (Fin n)) Ω Bool) (A : (Con Γ (Fin n) → ℤ) → Set Ω),
          (∀ f, MeasurableSet (A f)) →
          (∀ f, A f ⊆ {ω | σ.out ω f = true ↔ (Sat f).Nonempty}) →
          (2 / 3 : ENNReal) ≤ ∑' f, D f * μ (A f) →
          ∀ B : ℝ, σ.HasSize B → c * (n : ℝ) ^ degZLang Γ ≤ B := by sorry

end BoolCSPDel
