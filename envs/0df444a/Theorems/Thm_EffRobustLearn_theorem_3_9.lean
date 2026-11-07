-- Prove2me | Theorems.Thm_EffRobustLearn_theorem_3_9
-- name    : EffRobustLearn.theorem_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:41:56.80707+00:00
-- url     : https://prove2.me/theorems/043b5a35-1496-4026-b597-cc0b0e9ef012
-- title:
--   Theorem 3.9 — with an ERM oracle, Algorithm 1 learns to error $\eta+\varepsilon$ with $O(\varepsilon^{-4})$ calls (corrected: measurable, pointwise separable $C$)
-- statement:
--   There are universal constants $C_s,C_F,K_T,K_W>0$ and $D_W\in\mathbb N$ with the following property. Let $D$ be a distribution over $X$, let $C$ be a pointwise separable class of measurable concepts of finite VC dimension, $c^\star\in C$, $\eta\in[0,1)$ and $\varepsilon,\delta\in(0,1/2)$. Suppose
--   $$|\bar S_{\mathrm{inp}}|\ge C_s\frac{\mathrm{VCdim}(C)+\log(1/\delta)}{\varepsilon^2},\qquad|S_{\mathrm{ref}}|\ge C_s\frac{\mathrm{VCdim}(C)\log(2/\varepsilon)+\log(1/\delta)}{\varepsilon^4}.$$
--   Then for every adversary of rate $\eta$, every ERM oracle for $C$ and every initial concept $c_0\in C$, Algorithm 1 run with accuracy $\varepsilon$ and failure probability $\delta/3$ produces $\bar h_T$ such that, with probability at least $1-\delta$ over the clean sample, $S_{\mathrm{ref}}$ and the algorithm's seed,
--   $$\mathrm{err}_D(h,c^\star)=\mathrm{err}_D(\bar h_T,c^\star)\le\eta+\varepsilon,$$
--   where $h(x)\sim\mathrm{Rad}(\bar h_T(x))$. On every run it uses at most $K_T\varepsilon^{-4}$ ERM calls and work at most $K_W(|\bar S_{\mathrm{inp}}|+|S_{\mathrm{ref}}|+1/\varepsilon+\log(1/\delta))^{D_W}$.
--
--   This is the paper's resolution of Blanc's question: the information-theoretically optimal error $\eta+\varepsilon$ is reachable by an algorithm that is polynomial relative to an ERM oracle.
--
--   Differences from the source:
--   - correction: $C$ any class of finite VC dimension → every concept measurable and $C$ pointwise separable (published UnderstandingML.PointwiseSeparable); reason: the printed statement is false: $X=\omega_1$ with the countable–cocountable measure, $C$ = indicators of initial segments $[0,\alpha]$ together with the constant $+1$, $\mathrm{VCdim}(C)=1$, $c^\star=+1$, $\eta=0$, the identity adversary and an ERM oracle returning only initial segments give $\mathrm{err}_D(\bar h_T,c^\star)=1$ on every sample
--   - reading: $\mathrm{sign}(0)$ unspecified → $\mathrm{sign}(0)=+1$; reason: $\mathrm{Maj}_k(C)\subseteq\{\pm1\}^X$ needs a $\pm1$ value
--   - reading: runs in time $\mathrm{poly}(|\bar S_{\mathrm{inp}}|,|S_{\mathrm{ref}}|,1/\varepsilon,\log(1/\delta))$ → unit-cost work $\sum_{t\le T}[(n+m)(t+k+2)+2N_t+1]$ bounded by $K_W(n+m+1/\varepsilon+\log(1/\delta))^{D_W}$; reason: no machine is defined over an arbitrary $X$; the base is at least $2$, so this covers every polynomial in the four quantities
--   - reading: any maximizer; an arbitrary $c\in C$; any $c_t$ at a zero gradient → every oracle $O$, every $c_0\in C$, and $c_t=O([\,])$ at a zero gradient, counted as a call; reason: the universal reading is the strongest, and $O([\,])$ ranges over $C$ as $O$ ranges
--   - encoding: sufficiently large $C$; $O(\cdot)$; poly → constants $C_s,C_F,K_T,K_W,D_W$ fixed before $X,D,C$ and the data; reason: the source's constants are universal
--   - encoding: $\mathrm{err}_D(h,c^\star)$ for randomized $h$ → $\mathrm{err}_D(\bar h_T,c^\star)$ by Definition 2.1; reason: they are equal, p.18
--   - encoding: independent samples in each weighted ERM call → inverse CDF of i.i.d. uniform seed coordinates; reason: same law, and the bad event is then controlled by an event of the seed alone
--   - encoding: adversary receives $\bar S_{\mathrm{cln}}$, replaces at most $\eta n$ examples → a function of the clean points, index-wise, quantified before the probability; reason: Definition 1.1 and §2's sample conventions
--   - encoding: $\Pr[\cdot]\ge1-\delta$ → the measure of the bad set $\le\delta$, an outer measure when the set is not measurable; reason: the adversary and the oracle are arbitrary functions, so the event need not be measurable; this is the strongest reading
--   - encoding: concepts and labels in $\{\pm1\}$; samples as sets of instances → Bool values read through pm; samples as indexed families; reason: same instances; §2's sample conventions keep repeated entries distinct
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Theorem 3.9, p.17 (PDF p.18)

import Mathlib
import Definitions.Def_UnderstandingML_VC
import Definitions.Def_EffRobustLearn_errD
import Definitions.Def_EffRobustLearn_IsContaminationAdversary
import Definitions.Def_EffRobustLearn_IsERMOracle
import Definitions.Def_EffRobustLearn_alg1

open MeasureTheory

namespace EffRobustLearn

universe u

/-- Theorem 3.9 (Robust learning with access to an ERM oracle), p.17 (arXiv:2609.17655, held version, sha256 312a0857…), corrected: there are universal constants such that, for every distribution `D`, every pointwise separable class `C` of measurable concepts with finite VC dimension, `c⋆ ∈ C`, `η ∈ [0, 1)`, `ε, δ ∈ (0, 1/2)`, and sample sizes
`|S̄inp| ≥ C_s (VCdim(C) + log(1/δ))/ε²`, `|Sref| ≥ C_s (VCdim(C) log(2/ε) + log(1/δ))/ε⁴`, for every `η`-bounded adversary, every ERM oracle and every initial concept, Algorithm 1 run with accuracy `ε` and failure probability `δ/3` has
`err_D(h̄_T, c⋆) ≤ η + ε` with probability at least `1 - δ`, makes `O(ε⁻⁴)` ERM calls on every run, and does polynomial work on every run.

**Formalization Note.**
* The correction: as printed the theorem is false without a measurability condition on `C` (`X = ω₁` with the countable–cocountable measure, initial segments plus the constant `+1`). Measurable concepts and `UnderstandingML.PointwiseSeparable C` are the minimal fix.
* The probability is over the clean sample, the reference sample and the seed. It is the outer measure of the bad set, since `adv` and `O` need not be measurable, and they are quantified before the probability. The bound holds with no measurability of `adv` and `O` because the good events of Lemmas 3.11, C.5 and 3.8 can be taken
to depend on the clean sample, the reference sample and the seed only.
* The output `h(x) ∼ Rad(h̄_T(x))` has `err_D(h, c⋆) = err_D(h̄_T, c⋆)`, p.18.
* `C_F` is the constant of Fact 3.2's `O(·)`. `K_T`, `K_W`, `D_W` are the constants of `O(ε⁻⁴)` and `poly`. The base of the power is `≥ 2`, so any polynomial in the four quantities is covered. The cost model is `alg1`'s. -/
theorem theorem_3_9 :
    ∃ (Cs CF KT KW : ℝ) (DW : ℕ), 0 < Cs ∧ 0 < CF ∧ 0 < KT ∧ 0 < KW ∧
      ∀ (X : Type u) [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
        (C : Set (X → Bool)), (∀ c ∈ C, Measurable c) → UnderstandingML.PointwiseSeparable C →
        UnderstandingML.vcDim C < ⊤ → ∀ cstar ∈ C, ∀ η ε δ : ℝ,
        0 ≤ η → η < 1 → 0 < ε → ε < 1 / 2 → 0 < δ → δ < 1 / 2 →
        ∀ n m : ℕ,
          Cs * (((UnderstandingML.vcDim C).toNat : ℝ) + Real.log (1 / δ)) / ε ^ 2 ≤ n →
          Cs * (((UnderstandingML.vcDim C).toNat : ℝ) * Real.log (2 / ε) + Real.log (1 / δ)) / ε ^ 4 ≤ m →
        ∀ adv : (Fin n → X) → Fin n → X × Bool, IsContaminationAdversary η cstar adv →
        ∀ O : List (X × Bool) → X → Bool, IsERMOracle C O → ∀ c0 ∈ C,
          ((Measure.pi fun _ : Fin n => D).prod
              ((Measure.pi fun _ : Fin m => D).prod seedLaw))
            {p | η + ε < errD D (alg1 O CF ε (δ / 3) c0 (adv p.1) p.2.1 p.2.2).hbar (toPM cstar)} ≤
            ENNReal.ofReal δ ∧
          ∀ (Sinp : Fin n → X × Bool) (Sref : Fin m → X) (ω : ℕ × ℕ → unitInterval),
            ((alg1 O CF ε (δ / 3) c0 Sinp Sref ω).calls : ℝ) ≤ KT * (1 / ε) ^ 4 ∧
            ((alg1 O CF ε (δ / 3) c0 Sinp Sref ω).work : ℝ) ≤
              KW * ((n : ℝ) + m + 1 / ε + Real.log (1 / δ)) ^ DW := by sorry

end EffRobustLearn
