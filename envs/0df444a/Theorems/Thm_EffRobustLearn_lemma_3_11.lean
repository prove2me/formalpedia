-- Prove2me | Theorems.Thm_EffRobustLearn_lemma_3_11
-- name    : EffRobustLearn.lemma_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:35:25.215963+00:00
-- url     : https://prove2.me/theorems/91bfec66-1f3f-4448-a33e-5a2ce8823e0a
-- title:
--   Lemma 3.11 — the certificate of $c^\star$ is at most $\eta+\varepsilon/2$ (corrected: measurable, pointwise separable $C$)
-- statement:
--   There is a universal constant $C_s>0$ with the following property. Let $C$ be a pointwise separable class of measurable concepts of finite VC dimension, $D$ a distribution, $c^\star\in C$, $\eta\in[0,1)$, $\varepsilon>0$, $\delta\in(0,1)$. If
--   $$|\bar S_{\mathrm{inp}}|,|S_{\mathrm{ref}}|\ge C_s\frac{\mathrm{VCdim}(C)+\log(4/\delta)}{\varepsilon^2},$$
--   then for every adversary of rate $\eta$, with probability at least $1-\delta$ over the clean sample and $S_{\mathrm{ref}}$,
--   $$\sup_{\bar\mu\in\mathrm{conv}(C)}\eta(c^\star,\bar\mu;\bar S_{\mathrm{inp}},S_{\mathrm{ref}})\le\eta+\frac\varepsilon2.$$
--
--   This is the statistical half for the target concept: $c^\star$ is never ruled out by the certificate.
--
--   Differences from the source:
--   - correction: $C$ of finite VC dimension → every concept measurable and $C$ pointwise separable; reason: the printed statement fails for $X=\omega_1$ with the countable–cocountable measure, $C$ = initial segments and the constant $+1$, $c^\star=+1$, $\eta=0$, the identity adversary, $\varepsilon<1$: the set of samples with every input point below every reference point has outer measure $1$ and on it $\mu=c_\alpha$ with $\alpha$ between them gives certificate $1/2$
--   - encoding: $c^\star$, the adversary, $\eta$, $\varepsilon$, $\delta$ implicit → $c^\star\in C$, $\eta\in[0,1)$, $\varepsilon>0$, $\delta\in(0,1)$, every adversary before the probability; reason: the setting of Definition 1.1 and of the proof
--   - encoding: $\Pr[\cdot]\ge1-\delta$ → the measure of the bad set $\le\delta$, an outer measure when the set is not measurable; reason: the adversary and the oracle are arbitrary functions, so the event need not be measurable; this is the strongest reading
--   - encoding: concepts and labels in $\{\pm1\}$; samples as sets of instances → Bool values read through pm; samples as indexed families; reason: same instances; §2's sample conventions keep repeated entries distinct
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Lemma 3.11, eq. (3.10), p.17 (PDF p.18)

import Mathlib
import Definitions.Def_UnderstandingML_VC
import Definitions.Def_EffRobustLearn_certificate
import Definitions.Def_EffRobustLearn_IsContaminationAdversary

open MeasureTheory

namespace EffRobustLearn

universe u

/-- Lemma 3.11 (Certificate guarantee), p.17 (arXiv:2609.17655, held version, sha256 312a0857…). There is a universal `C_s > 0` such that if
`|S̄inp|, |Sref| ≥ C_s (VCdim(C) + log(4/δ))/ε²` then, for every `η`-bounded adversary, with probability at least `1 - δ`,
`sup_{μ̄∈conv(C)} η(c⋆, μ̄; S̄inp, Sref) ≤ η + ε/2`.

**Formalization Note.** The paper's "`c⋆`" and "under bounded contamination" are made explicit. The probability is over the clean sample and the reference sample, and is the outer measure of the bad set, since the adversary need not be measurable; the adversary is
quantified before the probability. Measurable concepts and pointwise separability are the correction. The inner `sSup` is over a nonempty bounded image. -/
theorem lemma_3_11 :
    ∃ Cs : ℝ, 0 < Cs ∧
      ∀ (X : Type u) [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
        (C : Set (X → Bool)), (∀ c ∈ C, Measurable c) → UnderstandingML.PointwiseSeparable C →
        UnderstandingML.vcDim C < ⊤ → ∀ cstar ∈ C, ∀ η ε δ : ℝ, 0 ≤ η → η < 1 → 0 < ε → 0 < δ → δ < 1 →
        ∀ n m : ℕ,
          Cs * (((UnderstandingML.vcDim C).toNat : ℝ) + Real.log (4 / δ)) / ε ^ 2 ≤ n →
          Cs * (((UnderstandingML.vcDim C).toNat : ℝ) + Real.log (4 / δ)) / ε ^ 2 ≤ m →
        ∀ adv : (Fin n → X) → Fin n → X × Bool, IsContaminationAdversary η cstar adv →
          ((Measure.pi fun _ : Fin n => D).prod (Measure.pi fun _ : Fin m => D))
            {p | η + ε / 2 < sSup ((fun μ : X → ℝ => certificate (toPM cstar) μ (adv p.1) p.2) ''
                convexHull ℝ (toPM '' C))} ≤ ENNReal.ofReal δ := by sorry

end EffRobustLearn
