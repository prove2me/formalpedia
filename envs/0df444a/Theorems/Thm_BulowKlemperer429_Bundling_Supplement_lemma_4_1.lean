-- Prove2me | Theorems.Thm_BulowKlemperer429_Bundling_Supplement_lemma_4_1
-- name    : BulowKlemperer429.Bundling.Supplement.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:37:56.986383+00:00
-- url     : https://prove2.me/theorems/e4c7a688-2bbd-4fc7-b8b6-9799dcc103ed
-- title:
--   Lemma 4.1 — tensorization of functional entropy over independent coordinates
-- statement:
--   Let $V=(V_1,\dots,V_m)$ have independent coordinates, $V_j\sim\nu_j$, and let $Z=Z(V)$ be a bounded nonnegative measurable function of $V$. For a law $\mu$ and a bounded nonnegative $f$, the functional entropy is $\mathrm{Ent}_\mu(f)=\mathbb E_\mu[f\log f]-\mathbb E_\mu[f]\log\mathbb E_\mu[f]$, with natural logarithm and $0\log0=0$. Then
--   $$\mathrm{Ent}(Z)\le\sum_{j=1}^m\mathbb E_{V_{-j}}\big[\mathrm{Ent}_{V_j}(Z)\big],$$
--   where $\mathrm{Ent}_{V_j}(Z)$ is the entropy of $Z$ as a function of $V_j$ alone, with the other coordinates $V_{-j}$ held fixed, and the outer expectation averages over $V_{-j}$.
--
--   This is the tensorization of entropy over independent coordinates ([Cha04, Proposition 12]); the paper applies it to threshold indicators to obtain Lemma 4.2.
--
--   **Formalization Note** Coordinates live in arbitrary measurable spaces; the index set is any finite type. Boundedness is pointwise, $0\le Z\le C$. Entropies are real Bochner integrals, legitimate because $Z$ is bounded. The inner entropy is computed for the slice $x\mapsto Z(v_{-j},x)$ and then integrated against the full product law, which equals averaging over $V_{-j}$ because the slice ignores $v_j$.
--
--   Differences from the source:
--   - generalization: V = (V_1, …, V_m) with independent coordinates (real valued in every use) → a finite index type and coordinates in arbitrary measurable spaces α j with probability laws ν j, V distributed as Measure.pi ν; reason: every real or nonnegative coordinate setting is the special case α j = ℝ or ℝ≥0; the statement is purely measure theoretic
--   - encoding: E_{V−j}[· computed over V_j with V−j fixed] → outer integral over the full product law of the slice x ↦ (function of Function.update v j x); reason: the slice does not depend on v_j, so integrating it against the product law equals averaging over V_{−j}
--   - encoding: Ent with natural logarithm and 0 log 0 := 0 → real Bochner integrals with Mathlib's Real.log, where Real.log 0 = 0; reason: Z is bounded, so every integral is finite and every integrand integrable; the convention 0 log 0 = 0 is Lean's
-- source:
--   Yichen Huang, STOC 2027 submission #429 (October 2026), p. 13, Lemma 4.1; proof Appendix B p. 23 (PDF p. 24) (PDF p. 14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/429.pdf

import Mathlib
import Definitions.Def_BulowKlemperer429_Bundling_Supplement_Entropy
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace BulowKlemperer429.Bundling.Supplement

theorem lemma_4_1 {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type}
    [∀ j, MeasurableSpace (α j)] (ν : ∀ j, Measure (α j)) [∀ j, IsProbabilityMeasure (ν j)]
    (Z : (∀ j, α j) → ℝ) (hZ : Measurable Z) (hbdd : ∃ C : ℝ, ∀ v, 0 ≤ Z v ∧ Z v ≤ C) :
    functionalEntropy (Measure.pi ν) Z ≤
      ∑ j, ∫ v, functionalEntropy (ν j) (fun x => Z (Function.update v j x)) ∂Measure.pi ν := by sorry


end BulowKlemperer429.Bundling.Supplement
