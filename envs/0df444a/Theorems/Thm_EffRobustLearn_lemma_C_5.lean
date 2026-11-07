-- Prove2me | Theorems.Thm_EffRobustLearn_lemma_C_5
-- name    : EffRobustLearn.lemma_C_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:34:59.49619+00:00
-- url     : https://prove2.me/theorems/e4aa8f50-db7f-4b74-9cbc-73954eb52862
-- title:
--   Lemma C.5 — uniform deviation over $\mathrm{conv}(\mathrm{Maj}_k(C))$ (corrected: measurable, pointwise separable $C$)
-- statement:
--   There is a universal constant $C_s>0$ with the following property. Let $C$ be a pointwise separable class of measurable concepts of finite VC dimension, $D$ a distribution, $c^\star\in C$, $k\ge1$, $\varepsilon>0$, $\delta\in(0,1)$. If
--   $$|S_{\mathrm{ref}}|\ge C_s\frac{\mathrm{VCdim}(C)k\log(2k)+\log(4/\delta)}{\varepsilon^2},$$
--   then, with probability at least $1-\delta$ over $S_{\mathrm{ref}}\sim D^{|S_{\mathrm{ref}}|}$,
--   $$\sup_{\bar h\in\mathrm{conv}(\mathrm{Maj}_k(C))}\big|\widehat{\mathrm{err}}_{S_{\mathrm{ref}}}(\bar h,c^\star)-\mathrm{err}_D(\bar h,c^\star)\big|\le\frac\varepsilon4.$$
--
--   It transfers the empirical guarantee on $S_{\mathrm{ref}}$ to the distribution $D$.
--
--   Differences from the source:
--   - correction: $C$ of finite VC dimension → every concept measurable and $C$ pointwise separable; reason: the printed statement is false for $X=\omega_1$ with the countable–cocountable measure, $C$ = initial segments and the constant $+1$, $c^\star=+1$, $k=1$: for $\alpha$ above the sample, $\mathrm{err}_D(c_\alpha,c^\star)=1$ and the empirical error is $0$, on every sample
--   - reading: $k\in\mathbb N$ → $k\ge1$; reason: (2.2) defines $\mathrm{maj}_k$ for integers $k\ge1$
--   - encoding: $\Pr[\cdot]\ge1-\delta$ → the $D^m$ measure of the bad set $\le\delta$, an outer measure if the set is not measurable; reason: same event; the bound on the measure is the strongest reading
--   - encoding: concepts and labels in $\{\pm1\}$; samples as sets of instances → Bool values read through pm; samples as indexed families; reason: same instances; §2's sample conventions keep repeated entries distinct
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Lemma C.5, eq. (C.5), p.43 (PDF p.44)

import Mathlib
import Definitions.Def_UnderstandingML_VC
import Definitions.Def_EffRobustLearn_MajClass
import Definitions.Def_EffRobustLearn_errD

open MeasureTheory

namespace EffRobustLearn

universe u

/-- Lemma C.5 (Statistical guarantee), p.43 (arXiv:2609.17655, held version, sha256 312a0857…). There is a universal `C_s > 0` such that if
`|Sref| ≥ C_s (VCdim(C) k log(2k) + log(4/δ))/ε²` then, with probability at least `1 - δ`,
`sup_{h̄∈conv(Maj_k(C))} |err̂_{Sref}(h̄, c⋆) - err_D(h̄, c⋆)| ≤ ε/4`.

**Formalization Note.** `k ≥ 1`, the range of (2.2). The probability is the `D^m` measure of the bad set, an outer measure if not measurable. Measurable concepts and
pointwise separability are the correction. The `sSup` is over a nonempty bounded image. Each `h̄` is measurable and bounded, so `err_D` is not a junk value. -/
theorem lemma_C_5 :
    ∃ Cs : ℝ, 0 < Cs ∧
      ∀ (X : Type u) [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
        (C : Set (X → Bool)), (∀ c ∈ C, Measurable c) → UnderstandingML.PointwiseSeparable C →
        UnderstandingML.vcDim C < ⊤ → ∀ cstar ∈ C, ∀ k : ℕ, 1 ≤ k → ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
        ∀ m : ℕ,
          Cs * (((UnderstandingML.vcDim C).toNat : ℝ) * (k : ℝ) * Real.log (2 * (k : ℝ)) +
            Real.log (4 / δ)) / ε ^ 2 ≤ m →
          (Measure.pi fun _ : Fin m => D)
            {r | ε / 4 < sSup ((fun h : X → ℝ =>
                |errHat r h (toPM cstar) - errD D h (toPM cstar)|) ''
                convexHull ℝ (toPM '' MajClass k C))} ≤ ENNReal.ofReal δ := by sorry

end EffRobustLearn
