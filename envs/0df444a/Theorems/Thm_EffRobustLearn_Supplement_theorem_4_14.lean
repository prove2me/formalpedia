-- Prove2me | Theorems.Thm_EffRobustLearn_Supplement_theorem_4_14
-- name    : EffRobustLearn.Supplement.theorem_4_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:21:10.3917+00:00
-- url     : https://prove2.me/theorems/366331f0-2809-42c2-bd86-1d549210ce44
-- title:
--   Theorem 4.14 — structured $L_1$ approximation of degree $\ell$ and error $\varepsilon/512$ gives error $\eta+\varepsilon$ with Algorithm 3
-- statement:
--   Let $D$ be an $A$-hypercontractive distribution on $\mathbb R^d$ and let $\varepsilon,\delta\in(0,1)$. Suppose $\mathcal C$ admits structured $L_1$ approximation (Definition 4.13) of degree $\ell\ge1$ and error $\varepsilon/512$, and let $c^\star\in\mathcal C$, $\eta\in[0,1)$. Under the sample size bounds of Theorem 4.7,
--   $$
--   |\bar S_{\mathrm{inp}}|\ge\frac{(C^\star A(d+1))^{4\ell}}{\varepsilon^3}\log\frac{16}\delta,\qquad |S_{\mathrm{ref}}|\ge\frac{(C^\star A(d+1))^{4\ell}}{\varepsilon^3}\Big(\log\frac{16}\delta\Big)^{8\ell+1},
--   $$
--   for a sufficiently large universal constant $C^\star$, Algorithm 3 runs in time $\mathrm{poly}(|\bar S_{\mathrm{inp}}|,|S_{\mathrm{ref}}|,(d+1)^\ell)$ and outputs a randomized hypothesis $h$ such that, under $\eta$-bounded contamination, with probability at least $1-\delta$,
--   $$
--   \mathrm{err}_D(h,c^\star)\le\eta+\varepsilon .
--   $$
--
--   The proof of Theorem 4.7 uses only two consequences of $L_2$ approximation, and noise-sensitivity bounds imply both at lower degree. This theorem gives the sharper runtimes of Table 1 (halfspaces, intersections of halfspaces, monotone functions).
--
--   **Formalization Note** Conventions as in Theorem 4.7: universal constants first, the runtime as an explicit work count with existence of a run, the outer measure of the bad set over the clean and reference samples, every run of the relational Algorithm 3.
--
--   Differences from the source:
--   - reading: "runs in time poly(|S̄inp|, |Sref|, (d + 1)^ℓ)" (no machine named; convex subproblems and a pseudoinverse square root) → on every input a run of Algorithm 3 exists, and every run's unit-cost work count (alg3Work, with fixed polynomial charges for the convex subproblems and for M_ℓ^{-1/2}) is ≤ K(n + m + (d+1)^ℓ)^k, K and k universal and chosen first; reason: the paper fixes no machine and no exact real model for these primitives; same reading as the base mission's decision 8
--   - reading: Algorithm 3's "sufficiently large universal constant C" (line 3) → one universal constant Calg, existential and chosen with C⋆ before every instance parameter; reason: the algorithm is a fixed algorithm with some universal constant
--   - reading: p⋆ ∈ argmax over P (any maximizer) inside every WIPF call → Algorithm 3 as a run relation; the bound holds for every run (the bad event is: some run errs); reason: the source allows any maximizer; this is the strongest reading
--   - encoding: randomized output h(x) ∼ Rad(h̄_T(x)), err_D(h, c⋆) → err_D(h̄_T, toPM c⋆) with the published errD; reason: err_D(h, c⋆) = err_D(h̄_T, c⋆) (p.23)
--   - encoding: with probability at least 1 − δ → outer measure of the bad set under D^n ⊗ D^m ≤ δ, with the adversary quantified before it; reason: the adversary need not be measurable; same convention as the base goal
--   - reading: concepts c ∈ C ⊆ {±1}^X → measurable concepts ℝ^d → Bool read as ±1 by toPM; reason: measurability is implicit in L2(D)/L1(D) approximation and in err_D; no ERM over C occurs in §4, so no separability condition is needed
--   - encoding: Algorithm 3's input δ → not an argument of the run relation; reason: the body of Algorithm 3 never reads δ
--   - encoding: ψ_ℓ in orthonormal coordinates on the range of M_ℓ (p.19), K the radius-2 ball of those coordinates → ψ_ℓ = M_ℓ^{-1/2} x^{⊗ℓ} (pseudoinverse) in the full monomial coordinates, K the radius-2 Euclidean ball there; reason: w₁ = 0, every g_t lies in the range of M_ℓ and the projection onto the ball preserves it, so the iterates are the isometric image of the source's and q_{w_t}, h_t, h̄_T are the same
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Theorem 4.14, p.25 (PDF p.26); Definition 4.13, p.25; Theorem 4.7, p.22 (PDF p.23)

import Mathlib
import Definitions.Def_EffRobustLearn_toPM
import Definitions.Def_EffRobustLearn_errD
import Definitions.Def_EffRobustLearn_IsContaminationAdversary
import Definitions.Def_EffRobustLearn_Supplement_IsHypercontractive
import Definitions.Def_EffRobustLearn_Supplement_HasStructuredL1Approx
import Definitions.Def_EffRobustLearn_Supplement_IsAlg3Run

open MeasureTheory

namespace EffRobustLearn

namespace Supplement

/-- Theorem 4.14 (Robust learning via structured L1 approximation), p.25, PDF p.26 (arXiv:2609.17655 (held version, sha256 312a0857…)).
There are universal constants `C⋆`, `C` (Algorithm 3's constant) and runtime constants `K, k` such that: for every
`d`, every `A`-hypercontractive `D` on `ℝ^d`, `ε, δ ∈ (0, 1)`, every class `C` of measurable concepts admitting
structured `L1` approximation (Definition 4.13) of degree `ℓ ≥ 1` and error `ε/512`, every `c⋆ ∈ C`, `η ∈ [0, 1)`,
the sample sizes of Theorem 4.7, and every `η`-bounded adversary:
1. on every input Algorithm 3 has a run, and every run does at most `K (n + m + (d+1)^ℓ)^k` work;
2. with probability at least `1 − δ`, every run outputs `h̄_T` with `err_D(h̄_T, c⋆) ≤ η + ε`.

**Formalization Note.** Conventions as in `theorem_4_7`: outer measure of the bad set over `D^n ⊗ D^m`, the
adversary fixed first, every run of the relational Algorithm 3, `err_D(h, c⋆) = err_D(h̄_T, c⋆)`. -/
theorem theorem_4_14 :
    ∃ (Cstar Calg KW : ℝ) (kW : ℕ), 0 < Cstar ∧ 0 < Calg ∧ 0 < KW ∧
      ∀ (d : ℕ) (A : ℝ) (D : Measure (Fin d → ℝ)) [IsProbabilityMeasure D],
        IsHypercontractive D A →
        ∀ (C : Set ((Fin d → ℝ) → Bool)), (∀ c ∈ C, Measurable c) →
        ∀ (ℓ : ℕ), 1 ≤ ℓ → ∀ η ε δ : ℝ, 0 ≤ η → η < 1 → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        HasStructuredL1Approx D C ℓ (ε / 512) →
        ∀ cstar ∈ C, ∀ n m : ℕ,
          (Cstar * A * ((d : ℝ) + 1)) ^ (4 * ℓ) / ε ^ 3 * Real.log (16 / δ) ≤ n →
          (Cstar * A * ((d : ℝ) + 1)) ^ (4 * ℓ) / ε ^ 3 * Real.log (16 / δ) ^ (8 * ℓ + 1) ≤ m →
        ∀ adv : (Fin n → Fin d → ℝ) → Fin n → (Fin d → ℝ) × Bool,
          IsContaminationAdversary η cstar adv →
          (∀ (Sinp : Fin n → (Fin d → ℝ) × Bool) (Sref : Fin m → Fin d → ℝ),
            (∃ run : Alg3Run d n ℓ, IsAlg3Run Calg A ℓ ε Sinp Sref run) ∧
            ∀ run : Alg3Run d n ℓ, IsAlg3Run Calg A ℓ ε Sinp Sref run →
              (alg3Work Calg A ℓ ε m run : ℝ) ≤ KW * ((n : ℝ) + m + ((d : ℝ) + 1) ^ ℓ) ^ kW) ∧
          ((Measure.pi fun _ : Fin n => D).prod (Measure.pi fun _ : Fin m => D))
              {p | ∃ run : Alg3Run d n ℓ, IsAlg3Run Calg A ℓ ε (adv p.1) p.2 run ∧
                η + ε < errD D (alg3Hbar Calg A ℓ ε p.2 run) (toPM cstar)} ≤
            ENNReal.ofReal δ := by sorry

end Supplement

end EffRobustLearn
