-- Prove2me | Theorems.Thm_EffRobustLearn_lemma_3_8
-- name    : EffRobustLearn.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:42:05.076542+00:00
-- url     : https://prove2.me/theorems/991641b9-8247-49fa-a7eb-a84d37627e91
-- title:
--   Lemma 3.8 — each Frank–Wolfe step is one weighted ERM call
-- statement:
--   There are universal $C_F,K_T>0$ such that in every run of Algorithm 1, for all nonempty samples, ERM oracles, initial concepts, $\varepsilon>0$ and failure parameter $\delta>0$, and every $t\in[T]$:
--
--   1. for every $c\in C$, $\frac1{|\bar S_{\mathrm{inp}}|+|S_{\mathrm{ref}}|}\big(\sum_{(x,y)\in\bar S_{\mathrm{inp}}}w_t(x,y)c(x)y+\sum_{x\in S_{\mathrm{ref}}}w_t(x,1)c(x)\big)=\langle\nabla F_t(\bar\mu_t[S]),c[S]\rangle$, with the weights (3.8);
--   2. the maximum of $\langle\nabla F_t(\bar\mu_t[S]),\cdot\rangle$ over $K$ equals its maximum over $\{c[S]:c\in C\}$;
--   3. $|w_t|\le 3(|\bar S_{\mathrm{inp}}|+|S_{\mathrm{ref}}|)T^{1/4}/\min(|\bar S_{\mathrm{inp}}|,|S_{\mathrm{ref}}|)$.
--
--   With probability at least $1-\delta$ over the seed, all $T$ steps achieve additive accuracy $\gamma_t/25$. Every run uses at most $T$ ERM calls, and at most $K_T\varepsilon^{-4}$ when $\varepsilon\le1$.
--
--   Differences from the source:
--   - encoding: Lemma 3.8's prose → the conjuncts (identity, max over $K$, weight bound, accuracy, call count); reason: the first three are what "is a weighted ERM problem" means in the proof on p.16
--   - reading: no call when $\nabla F_t(\bar\mu_t[S])=0$ → $c_t=O([\,])$, counted as a call; reason: every concept is a maximizer, $O([\,])$ ranges over $C$ as $O$ ranges, and the bound $T$ still holds
--   - reading: $T=O(\varepsilon^{-4})$ → $T\le K_T\varepsilon^{-4}$ for $\varepsilon\le1$; reason: for large $\varepsilon$ the ceiling makes $T=1$ while $\varepsilon^{-4}\to0$, so an $O(\cdot)$ needs bounded $\varepsilon$; the theorem has $\varepsilon<1/2$
--   - encoding: calls of Fact 3.2 with $O(\cdot)$ samples → the sampler with constant $C_F$ on an explicit seed; reason: see Fact 3.2
--   - encoding: $\Pr[\cdot]\ge1-\delta$ → the measure of the bad set $\le\delta$, an outer measure when the set is not measurable; reason: the adversary and the oracle are arbitrary functions, so the event need not be measurable; this is the strongest reading
--   - encoding: concepts and labels in $\{\pm1\}$; samples as sets of instances → Bool values read through pm; samples as indexed families; reason: same instances; §2's sample conventions keep repeated entries distinct
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Lemma 3.8, p.15 (PDF p.16), with its proof, p.16 (PDF p.17)

import Mathlib
import Definitions.Def_EffRobustLearn_alg1
import Definitions.Def_EffRobustLearn_gradF
import Definitions.Def_EffRobustLearn_IsERMOracle

open MeasureTheory

namespace EffRobustLearn

universe u

/-- Lemma 3.8 (ERM reduction), p.15 (arXiv:2609.17655, held version, sha256 312a0857…). There is a universal `C_F` such that in every run of Algorithm 1, for all `n, m ≥ 1`, samples, ERM oracles, initial concepts,
`ε > 0` and failure parameter `δ > 0`, at each round `t ∈ [T]`: (i) the objective `⟨∇F_t(μ̄_t[S]), c[S]⟩` is the weighted-ERM objective with weights (3.8); (ii) its maximum over `K`
is its maximum over `C`; (iii) the weights lie in `[-b, b]`, `b` being the weight bound of p.16; (iv) with outer probability at least `1 - δ` over the seed, all `T` steps achieve additive accuracy `γ_t/25`; and (v) every run uses at most `T` ERM calls, with `T ≤ K_T ε⁻⁴` for `ε ≤ 1`.

**Formalization Note.** Item (ii) takes real suprema of images of exactly `K` and `C`, which are
nonempty and finite-valued or compact, hence maxima. -/
theorem lemma_3_8 :
    ∃ CF KT : ℝ, 0 < CF ∧ 0 < KT ∧
      ∀ (X : Type u) (C : Set (X → Bool)) (O : List (X × Bool) → X → Bool), IsERMOracle C O →
        ∀ c0 ∈ C, ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ n m : ℕ, 0 < n → 0 < m →
        ∀ (Sinp : Fin n → X × Bool) (Sref : Fin m → X),
          (∀ ω : ℕ × ℕ → unitInterval, ∀ t ∈ Finset.Icc 1 (numRounds ε),
            (∀ c ∈ C, (1 / ((n : ℝ) + m)) *
                (∑ i, weightVec ε c0 (alg1 O CF ε δ c0 Sinp Sref ω).c Sinp Sref t (Sum.inl i) *
                    toPM c (Sinp i).1 * pm (Sinp i).2 +
                  ∑ j, weightVec ε c0 (alg1 O CF ε δ c0 Sinp Sref ω).c Sinp Sref t (Sum.inr j) *
                    toPM c (Sref j)) =
              inner ℝ (gradAtIterate ε c0 (alg1 O CF ε δ c0 Sinp Sref ω).c Sinp Sref t)
                (evalVec (toPM c) Sinp Sref)) ∧
            sSup ((fun v => inner ℝ (gradAtIterate ε c0 (alg1 O CF ε δ c0 Sinp Sref ω).c Sinp Sref t) v) ''
                feasibleSet C Sinp Sref) =
              sSup ((fun c : X → Bool =>
                inner ℝ (gradAtIterate ε c0 (alg1 O CF ε δ c0 Sinp Sref ω).c Sinp Sref t)
                  (evalVec (toPM c) Sinp Sref)) '' C) ∧
            ∀ a, |weightVec ε c0 (alg1 O CF ε δ c0 Sinp Sref ω).c Sinp Sref t a| ≤
              weightBound n m (numRounds ε)) ∧
          seedLaw {ω | ∃ t ∈ Finset.Icc 1 (numRounds ε), ∃ v ∈ feasibleSet C Sinp Sref,
              inner ℝ (gradAtIterate ε c0 (alg1 O CF ε δ c0 Sinp Sref ω).c Sinp Sref t)
                  (evalVec (toPM ((alg1 O CF ε δ c0 Sinp Sref ω).c t)) Sinp Sref) <
                inner ℝ (gradAtIterate ε c0 (alg1 O CF ε δ c0 Sinp Sref ω).c Sinp Sref t) v -
                  stepSize t / 25} ≤ ENNReal.ofReal δ ∧
          (∀ ω : ℕ × ℕ → unitInterval, (alg1 O CF ε δ c0 Sinp Sref ω).calls ≤ numRounds ε ∧
            (ε ≤ 1 → ((alg1 O CF ε δ c0 Sinp Sref ω).calls : ℝ) ≤ KT * (1 / ε) ^ 4)) := by sorry

end EffRobustLearn
