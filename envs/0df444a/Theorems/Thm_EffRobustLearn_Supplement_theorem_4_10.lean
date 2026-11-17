-- Prove2me | Theorems.Thm_EffRobustLearn_Supplement_theorem_4_10
-- name    : EffRobustLearn.Supplement.theorem_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:20:24.323881+00:00
-- url     : https://prove2.me/theorems/13e02175-daa2-4eba-93d6-0c09b48e3753
-- title:
--   Theorem 4.10 — under $N(0,I_d)$ or $\mathrm{Unif}\{\pm1\}^d$, $L_1$ approximators of degree $\ell$ give error $\eta+\varepsilon$ with Algorithm 3 at degree $\ell'=C_0\ell^2/\varepsilon^4$
-- statement:
--   Let $D$ be the standard Gaussian distribution on $\mathbb R^d$ or the uniform distribution on $\{\pm1\}^d$, and suppose $\mathcal C$ admits $L_1(D)$ polynomial approximators of degree $\ell\ge1$ with error $\varepsilon/8$. Let $c^\star\in\mathcal C$, $\eta\in[0,1)$ and $\varepsilon,\delta\in(0,1)$. Set $\ell'=C_0\ell^2/\varepsilon^4$ and suppose
--   $$
--   |\bar S_{\mathrm{inp}}|\ge\frac{(C^\star(d+1))^{4\ell'}}{\varepsilon^3}\log\frac{16}\delta,\qquad |S_{\mathrm{ref}}|\ge\frac{(C^\star(d+1))^{4\ell'}}{\varepsilon^3}\Big(\log\frac{16}\delta\Big)^{8\ell'+1}
--   $$
--   for sufficiently large universal constants $C_0$ and $C^\star$. Under $\eta$-bounded contamination, Algorithm 3 with degree $\ell'$, accuracy $\varepsilon/2$ and failure parameter $\delta/2$ runs in time $\mathrm{poly}(|\bar S_{\mathrm{inp}}|,|S_{\mathrm{ref}}|,(d+1)^{\ell'})$ and outputs a randomized hypothesis $h$ such that, with probability at least $1-\delta$,
--   $$
--   \mathrm{err}_D(h,c^\star)\le\eta+\varepsilon .
--   $$
--
--   This is the formal version of Theorem 1.5. It extends the $L_2$ result to the much larger family of classes with low-degree $L_1$ approximators (for instance halfspaces and their intersections) under the two standard distributions.
--
--   **Formalization Note** $\ell'$ is a degree, so it is $\lceil C_0\ell^2/\varepsilon^4\rceil$. The sample sizes contain no hypercontractivity constant, so Algorithm 3 is run with a universal constant $A_0\ge1$, chosen with $C_0$, $C^\star$, Algorithm 3's constant and the runtime constants. The uniform cube is a law on $\mathbb R^d$ supported on $\{\pm1\}^d$. The runtime and probability conventions are those of Theorem 4.7.
--
--   Differences from the source:
--   - reading: ℓ′ := C₀ℓ²/ε⁴ (used as a degree) → ℓ′ = ⌈C₀ℓ²/ε⁴⌉₊; reason: a degree must be a natural number; the ceiling is the only reading that makes it one
--   - reading: Algorithm 3's hypercontractivity constant A (no A in the sample sizes) → Algorithm 3 is run with a universal A₀ ≥ 1, existential and chosen with the other constants; reason: both laws are hypercontractive with a constant independent of d, which is why the sample sizes contain no A
--   - reading: "runs in time poly(|S̄inp|, |Sref|, (d + 1)^{ℓ′})" (no machine named; convex subproblems and a pseudoinverse square root) → on every input a run of Algorithm 3 (degree ℓ′, accuracy ε/2, A₀) exists, and every run's unit-cost work count is ≤ K(n + m + (d+1)^{ℓ′})^k, K and k universal and chosen first; reason: the paper fixes no machine and no exact real model for these primitives; same reading as the base mission's decision 8
--   - reading: Algorithm 3's "sufficiently large universal constant C" (line 3) → one universal constant Calg, existential and chosen with C⋆ before every instance parameter; reason: the algorithm is a fixed algorithm with some universal constant
--   - reading: p⋆ ∈ argmax over P (any maximizer) inside every WIPF call → Algorithm 3 as a run relation; the bound holds for every run (the bad event is: some run errs); reason: the source allows any maximizer; this is the strongest reading
--   - encoding: randomized output h(x) ∼ Rad(h̄_T(x)), err_D(h, c⋆) → err_D(h̄_T, toPM c⋆) with the published errD; reason: err_D(h, c⋆) = err_D(h̄_T, c⋆) (p.23)
--   - encoding: with probability at least 1 − δ → outer measure of the bad set under D^n ⊗ D^m ≤ δ, with the adversary quantified before it; reason: the adversary need not be measurable; same convention as the base goal
--   - reading: concepts c ∈ C ⊆ {±1}^X → measurable concepts ℝ^d → Bool read as ±1 by toPM; reason: measurability is implicit in L2(D)/L1(D) approximation and in err_D; no ERM over C occurs in §4, so no separability condition is needed
--   - encoding: failure parameter δ/2 passed to Algorithm 3 → not an argument of the run relation; reason: the body of Algorithm 3 never reads δ
--   - encoding: the uniform distribution on {±1}^d → the product of (δ₁ + δ₋₁)/2 on ℝ^d (unifCube); reason: a law on ℝ^d supported on the cube, so polynomials and concepts on ℝ^d apply; same instances
--   - reading: "polynomial (approximator) of degree ℓ" (Definition 4.2; L1(D) approximators in Theorem 4.10) → a polynomial q with totalDegree q ≤ ℓ; reason: the standard degree-at-most convention of polynomial approximation [KKMS08], also used by Definition 4.13; the proof only uses that q lies in the span of x^{⊗ℓ}
--   - encoding: ψ_ℓ in orthonormal coordinates on the range of M_ℓ (p.19), K the radius-2 ball of those coordinates → ψ_ℓ = M_ℓ^{-1/2} x^{⊗ℓ} (pseudoinverse) in the full monomial coordinates, K the radius-2 Euclidean ball there; reason: w₁ = 0, every g_t lies in the range of M_ℓ and the projection onto the ball preserves it, so the iterates are the isometric image of the source's and q_{w_t}, h_t, h̄_T are the same
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Theorem 4.10, p.24 (PDF p.25); Algorithm 3, p.20 (PDF p.21)

import Mathlib
import Definitions.Def_EffRobustLearn_toPM
import Definitions.Def_EffRobustLearn_errD
import Definitions.Def_EffRobustLearn_IsContaminationAdversary
import Definitions.Def_EffRobustLearn_Supplement_HasL1Approx
import Definitions.Def_EffRobustLearn_Supplement_stdGaussian
import Definitions.Def_EffRobustLearn_Supplement_IsAlg3Run

open MeasureTheory

namespace EffRobustLearn

namespace Supplement

/-- Theorem 4.10 (Robust learning via L1 approximation), p.24, PDF p.25 (arXiv:2609.17655 (held version, sha256 312a0857…)).
There are universal constants `C₀`, `C⋆`, Algorithm 3's constant `C`, a hypercontractivity constant `A₀ ≥ 1`
that Algorithm 3 is run with, and runtime constants `K, k` such that: for every `d`, `D = N(0, I_d)` or `D` uniform
on `{±1}^d`, every class `C` of measurable concepts with `L1(D)` approximators of degree `ℓ ≥ 1` and error `ε/8`,
every `c⋆ ∈ C`, `η ∈ [0, 1)`, `ε, δ ∈ (0, 1)`, with `ℓ′ := ⌈C₀ℓ²/ε⁴⌉`, every
`n ≥ ((C⋆(d+1))^{4ℓ′}/ε³) log(16/δ)`, `m ≥ ((C⋆(d+1))^{4ℓ′}/ε³)(log(16/δ))^{8ℓ′+1}` and every `η`-bounded adversary,
Algorithm 3 with degree `ℓ′` and accuracy `ε/2`:
1. has a run on every input, and every run does at most `K (n + m + (d+1)^{ℓ′})^k` work;
2. with probability at least `1 − δ`, every run outputs `h̄_T` with `err_D(h̄_T, c⋆) ≤ η + ε`.

**Formalization Note.**
* `ℓ′ = C₀ℓ²/ε⁴` is used as a degree, so it is read as `⌈C₀ℓ²/ε⁴⌉`.
* The sample sizes contain no `A`, so Algorithm 3 is run with a universal `A₀` (both laws are hypercontractive with a
  constant independent of `d`); `A₀` is chosen with the other constants.
* The failure parameter `δ/2` passed to Algorithm 3 is not read by its body, so it does not appear.
* Other conventions as in `theorem_4_7`. -/
theorem theorem_4_10 :
    ∃ (C0 Cstar Calg A0 KW : ℝ) (kW : ℕ), 0 < C0 ∧ 0 < Cstar ∧ 0 < Calg ∧ 1 ≤ A0 ∧ 0 < KW ∧
      ∀ (d : ℕ) (D : Measure (Fin d → ℝ)), (D = stdGaussian d ∨ D = unifCube d) →
        ∀ (C : Set ((Fin d → ℝ) → Bool)), (∀ c ∈ C, Measurable c) →
        ∀ (ℓ : ℕ), 1 ≤ ℓ → ∀ η ε δ : ℝ, 0 ≤ η → η < 1 → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        HasL1Approx D C ℓ (ε / 8) →
        ∀ cstar ∈ C, ∀ n m : ℕ,
          (Cstar * ((d : ℝ) + 1)) ^ (4 * ⌈C0 * (ℓ : ℝ) ^ 2 / ε ^ 4⌉₊) / ε ^ 3 *
              Real.log (16 / δ) ≤ n →
          (Cstar * ((d : ℝ) + 1)) ^ (4 * ⌈C0 * (ℓ : ℝ) ^ 2 / ε ^ 4⌉₊) / ε ^ 3 *
              Real.log (16 / δ) ^ (8 * ⌈C0 * (ℓ : ℝ) ^ 2 / ε ^ 4⌉₊ + 1) ≤ m →
        ∀ adv : (Fin n → Fin d → ℝ) → Fin n → (Fin d → ℝ) × Bool,
          IsContaminationAdversary η cstar adv →
          (∀ (Sinp : Fin n → (Fin d → ℝ) × Bool) (Sref : Fin m → Fin d → ℝ),
            (∃ run : Alg3Run d n ⌈C0 * (ℓ : ℝ) ^ 2 / ε ^ 4⌉₊,
              IsAlg3Run Calg A0 ⌈C0 * (ℓ : ℝ) ^ 2 / ε ^ 4⌉₊ (ε / 2) Sinp Sref run) ∧
            ∀ run : Alg3Run d n ⌈C0 * (ℓ : ℝ) ^ 2 / ε ^ 4⌉₊,
              IsAlg3Run Calg A0 ⌈C0 * (ℓ : ℝ) ^ 2 / ε ^ 4⌉₊ (ε / 2) Sinp Sref run →
              (alg3Work Calg A0 ⌈C0 * (ℓ : ℝ) ^ 2 / ε ^ 4⌉₊ (ε / 2) m run : ℝ) ≤
                KW * ((n : ℝ) + m + ((d : ℝ) + 1) ^ ⌈C0 * (ℓ : ℝ) ^ 2 / ε ^ 4⌉₊) ^ kW) ∧
          ((Measure.pi fun _ : Fin n => D).prod (Measure.pi fun _ : Fin m => D))
              {p | ∃ run : Alg3Run d n ⌈C0 * (ℓ : ℝ) ^ 2 / ε ^ 4⌉₊,
                IsAlg3Run Calg A0 ⌈C0 * (ℓ : ℝ) ^ 2 / ε ^ 4⌉₊ (ε / 2) (adv p.1) p.2 run ∧
                η + ε < errD D (alg3Hbar Calg A0 ⌈C0 * (ℓ : ℝ) ^ 2 / ε ^ 4⌉₊ (ε / 2) p.2 run)
                  (toPM cstar)} ≤
            ENNReal.ofReal δ := by sorry

end Supplement

end EffRobustLearn
