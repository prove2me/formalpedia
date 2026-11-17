-- Prove2me | Theorems.Thm_EffRobustLearn_Supplement_theorem_D_1
-- name    : EffRobustLearn.Supplement.theorem_D_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:18:40.312562+00:00
-- url     : https://prove2.me/theorems/0eb7f784-9d1a-45cd-b7fd-d7ef2a08a651
-- title:
--   Theorem D.1 — adaptive weighted iterative filtering: clean-point and weighted polynomial preservation
-- statement:
--   Let $D$ be an $A$-hypercontractive distribution on $\mathbb R^d$, let $\varepsilon,\delta\in(0,1)$ and $\ell\ge1$. There is a universal constant $C$ such that, if
--   $$
--   n=|\bar S_{\mathrm{inp}}|\ge\frac{(CA(d+1))^{4\ell}}{\varepsilon^3}\log\frac C\delta,\qquad m=|S_{\mathrm{ref}}|\ge\frac{(CA(d+1))^{4\ell}}{\varepsilon^3}\Big(\log\frac C\delta\Big)^{8\ell+1},
--   $$
--   then the following hold for calls of Algorithm 2 (WIPF) with the same parameters, the same $S_{\mathrm{ref}}$ and the normalization $n$, the first call on $\bar S_{\mathrm{inp}}$ and each later call on the previous output, with weights $v(x,y)=\frac{2+|m(x)|-ym(x)}{8(1+|m(x)|)}$.
--
--   1. **Clean-point preservation.** For every measurable target $c^\star$, every $\eta\in[0,1)$ and every $\eta$-bounded adversary, with probability at least $1-\delta$ over the clean sample $S_{\mathrm{cln}}\sim D^n$ and $S_{\mathrm{ref}}\sim D^m$: for every choice of the functions $m$ of the successive calls, every returned sample $\bar S_{\mathrm{filt}}$ satisfies
--   $$
--   \frac{|(S_{\mathrm{cln}}\cap S_{\mathrm{inp}})\setminus S_{\mathrm{filt}}|}{|\bar S_{\mathrm{inp}}|}-\frac{|(S_{\mathrm{inp}}\setminus S_{\mathrm{cln}})\setminus S_{\mathrm{filt}}|}{|\bar S_{\mathrm{inp}}|}\le\frac{\varepsilon}{32}.
--   $$
--   2. **Weighted polynomial preservation.** For every polynomial $p$ of degree at most $2\ell$ with $\mathbb E_{x\sim D}|p(x)|\le\varepsilon/128$, with probability at least $1-\delta$ over $S_{\mathrm{ref}}$: $p\in\mathcal P$, and every call with any function $m$ returns $\bar S_{\mathrm{filt}}$ with
--   $$
--   \Big|\frac1{|\bar S_{\mathrm{inp}}|}\sum_{(x,y)\in\bar S_{\mathrm{filt}}}v(x,y)\,p(x)\Big|\le\frac{\varepsilon}{64}.
--   $$
--   3. **Runtime.** Each call has a run, and every run takes work at most $K\,(n+m+(d+1)^{2\ell})^k$ for universal constants $K,k$.
--
--   This is the filtering guarantee behind Algorithm 3. The adversary may adapt the weight functions to earlier outputs, and the first part still bounds the number of clean examples lost.
--
--   **Formalization Note** $S_{\mathrm{cln}}\cap S_{\mathrm{inp}}$ is the set of indices the adversary left unchanged, and $S_{\mathrm{inp}}\setminus S_{\mathrm{cln}}$ the replaced ones (index-wise replacement, the base mission's `IsContaminationAdversary`). Probabilities are outer measures of the bad sets.
--
--   Differences from the source:
--   - reading: "the function m may change between calls based on previous outputs" (adaptive m) → part 1: inside the probability, for every K, every sequence m₁, m₂, … and every chain of runs, every output satisfies the bound; reason: the proof's event depends only on Scln and Sref, so every adaptive rule is covered
--   - generalization: part 2: every call of the chain with function m returns S̄filt with the bound → every run of Algorithm 2 on any input sub-sample of any corrupted sample, with any m, returns S̄filt with the bound; reason: the proof uses only p ∈ P and the return test λ⋆ ≤ ε/64 (with −p ∈ P); specializes to the calls of the chain
--   - reading: "each call can be implemented in time poly(|S̄inp|, |Sref|, (d + 1)^{2ℓ})" → every input has a run, and every run's unit-cost work count wipfWork is ≤ K(n + m + (d+1)^{2ℓ})^k with K, k universal; reason: the paper fixes no machine; the convex subproblems are charged a fixed polynomial (base decision 8)
--   - reading: p⋆ ∈ argmax over P (any maximizer) inside every WIPF call → Algorithm 2 as a run relation; the guarantees hold for every run; reason: the source allows any maximizer; this is the strongest reading
--   - encoding: Scln ∩ Sinp and Sinp \ Scln → indices j with adv s j = (s j, c⋆(s j)) and indices with adv s j ≠ (s j, c⋆(s j)); reason: index-wise replacement of the published IsContaminationAdversary keeps the instance identities of §2
--   - reading: c⋆ and η of the standing setting (D.1 names neither) → every measurable c⋆, every η ∈ [0, 1) and every η-bounded adversary; reason: η plays no role in the proof; concepts are measurable in §4
--   - encoding: with probability at least 1 − δ (over Scln, Sref; over Sref) → outer measure of the bad set under D^n ⊗ D^m, resp. D^m, ≤ δ; reason: the adversary and the runs need not be measurable; same convention as the base goal
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Theorem D.1, p.44 (PDF p.45); Algorithm 2, p.20 (PDF p.21)

import Mathlib
import Definitions.Def_EffRobustLearn_IsContaminationAdversary
import Definitions.Def_EffRobustLearn_Supplement_IsHypercontractive
import Definitions.Def_EffRobustLearn_Supplement_IsWIPFRun

open MeasureTheory

namespace EffRobustLearn

namespace Supplement

open Classical in
/-- Theorem D.1 (Adaptive weighted iterative filtering), p.44, PDF p.45 (arXiv:2609.17655 (held version, sha256 312a0857…)).
There are a universal constant `C` and runtime constants `K, k` such that, for every `d`, every `A`-hypercontractive
`D` on `ℝ^d`, `ε, δ ∈ (0, 1)`, `ℓ ≥ 1`, `n = |S̄inp| ≥ ((CA(d+1))^{4ℓ}/ε³) log(C/δ)` and
`m = |Sref| ≥ ((CA(d+1))^{4ℓ}/ε³)(log(C/δ))^{8ℓ+1}`:
1. **Clean-point preservation.** For every measurable target `c⋆`, `η ∈ [0, 1)` and `η`-bounded adversary, with
   probability at least `1 − δ` over the clean and reference samples: for every chain of calls of Algorithm 2 (the
   first on all of `S̄inp`, each later one on the previous output, all with the same `Sref` and normalization `n`, and
   weight functions `m₁, m₂, …` chosen arbitrarily, hence adaptively), every output `S̄filt` has
   `|(Scln ∩ Sinp) \ Sfilt|/n − |(Sinp \ Scln) \ Sfilt|/n ≤ ε/32`.
2. **Weighted polynomial preservation.** For every polynomial `p` of degree at most `2ℓ` with `E_D|p| ≤ ε/128`, with
   probability at least `1 − δ` over `Sref`: `p ∈ P`, and every call of Algorithm 2, with any function `m`,
   returns `S̄filt` with `|(1/n) ∑_{(x,y)∈S̄filt} v(x, y) p(x)| ≤ ε/64`.
3. **Runtime.** Every call has a run, and every run does at most `K (n + m + (d+1)^{2ℓ})^k` work.

**Formalization Note.**
* `Scln ∩ Sinp` is the set of indices the adversary left unchanged and `Sinp \ Scln` the replaced ones (index-wise
  replacement, the published `IsContaminationAdversary`).
* Probabilities are outer measures of the bad sets; part 1 is over `D^n ⊗ D^m`, part 2 over `D^m` only.
* Part 2 is stated uniformly over every corrupted sample, every input sub-sample and every weight function. -/
theorem theorem_D_1 :
    ∃ (Cc KW : ℝ) (kW : ℕ), 0 < Cc ∧ 0 < KW ∧
      ∀ (d : ℕ) (A : ℝ) (D : Measure (Fin d → ℝ)) [IsProbabilityMeasure D],
        IsHypercontractive D A →
        ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 → ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ n m : ℕ,
          (Cc * A * ((d : ℝ) + 1)) ^ (4 * ℓ) / ε ^ 3 * Real.log (Cc / δ) ≤ n →
          (Cc * A * ((d : ℝ) + 1)) ^ (4 * ℓ) / ε ^ 3 * Real.log (Cc / δ) ^ (8 * ℓ + 1) ≤ m →
        (∀ (cstar : (Fin d → ℝ) → Bool), Measurable cstar → ∀ η : ℝ, 0 ≤ η → η < 1 →
          ∀ adv : (Fin n → Fin d → ℝ) → Fin n → (Fin d → ℝ) × Bool,
            IsContaminationAdversary η cstar adv →
            ((Measure.pi fun _ : Fin n => D).prod (Measure.pi fun _ : Fin m => D))
                {p | ∃ (K : ℕ) (ms : ℕ → (Fin d → ℝ) → ℝ) (F : ℕ → Finset (Fin n)) (ks : ℕ → ℕ),
                  F 0 = Finset.univ ∧
                  (∀ i < K, IsWIPFRun ℓ A ε (adv p.1) p.2 (ms i) (F i) (F (i + 1)) (ks i)) ∧
                  ∃ i ≤ K, ε / 32 <
                    ((Finset.univ.filter fun j =>
                        adv p.1 j = (p.1 j, cstar (p.1 j)) ∧ j ∉ F i).card : ℝ) / n -
                    ((Finset.univ.filter fun j =>
                        adv p.1 j ≠ (p.1 j, cstar (p.1 j)) ∧ j ∉ F i).card : ℝ) / n} ≤
              ENNReal.ofReal δ) ∧
        (∀ q : MvPolynomial (Fin d) ℝ, q.totalDegree ≤ 2 * ℓ →
          ∫⁻ x, ‖MvPolynomial.eval x q‖ₑ ∂D ≤ ENNReal.ofReal (ε / 128) →
          (Measure.pi fun _ : Fin m => D)
              {r | ¬ (q ∈ filterFamily ℓ A ε r ∧
                ∀ (Sinp : Fin n → (Fin d → ℝ) × Bool) (mf : (Fin d → ℝ) → ℝ)
                  (S out : Finset (Fin n)) (k : ℕ), IsWIPFRun ℓ A ε Sinp r mf S out k →
                  |(1 / (n : ℝ)) * filtObj Sinp mf out q| ≤ ε / 64)} ≤
            ENNReal.ofReal δ) ∧
        (∀ (Sinp : Fin n → (Fin d → ℝ) × Bool) (Sref : Fin m → Fin d → ℝ)
            (mf : (Fin d → ℝ) → ℝ) (S : Finset (Fin n)),
          (∃ (out : Finset (Fin n)) (k : ℕ), IsWIPFRun ℓ A ε Sinp Sref mf S out k) ∧
          ∀ (out : Finset (Fin n)) (k : ℕ), IsWIPFRun ℓ A ε Sinp Sref mf S out k →
            (wipfWork (Fintype.card (MonoIdx d (2 * ℓ))) S.card m k : ℝ) ≤
              KW * ((n : ℝ) + m + ((d : ℝ) + 1) ^ (2 * ℓ)) ^ kW) := by sorry

end Supplement

end EffRobustLearn
