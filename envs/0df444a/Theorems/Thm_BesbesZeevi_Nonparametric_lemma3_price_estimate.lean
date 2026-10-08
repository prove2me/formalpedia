-- Prove2me | Theorems.Thm_BesbesZeevi_Nonparametric_lemma3_price_estimate
-- name    : BesbesZeevi.Nonparametric.lemma3_price_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:50:32.863694+00:00
-- url     : https://prove2.me/theorems/8e57b40d-bbb5-46b0-8768-6ce195f5ef87
-- title:
--   Lemma 3: $\mathbb P\{r(\lambda(p^D))-r(\lambda(\hat p))>C_1u_n\}\le C_3/n^{\eta-1}$ and $\mathbb P\{|\hat p^c-p^c|>C_2u_n\}\le C_3/n^{\eta-1}$
-- statement:
--   Use the tuning of Proposition 1, $\tau_n\asymp n^{-1/4}$ and $\kappa_n\asymp n^{1/4}$, and let $u_n=(\log n)^{1/2}\max\{1/\kappa_n,(n\Delta_n)^{-1/2}\}$, with $\eta=2$. There are constants $C_1,C_2,C_3>0$, independent of the demand function and of $n$, with the following property.
--
--   Let $\lambda\in\mathcal L$, let $p^u$ maximize $p\lambda(p)$ and $p^c$ minimize $|\lambda(p)-x/T|$ over $[\underline p,\overline p]$, and put $p^D=\max\{p^u,p^c\}$. Let $\hat p^c$ and $\hat p$ be Algorithm 1's estimates. Then for all $n\ge1$,
--
--   $$
--   \mathbb P\big\{r(\lambda(p^D))-r(\lambda(\hat p))>C_1u_n\big\}\le\frac{C_3}{n^{\eta-1}},\qquad
--   \mathbb P\big\{|\hat p^c-p^c|>C_2u_n\big\}\le\frac{C_3}{n^{\eta-1}},
--   $$
--
--   where $r(\lambda(p))=p\lambda(p)$.
--
--   The learned price is thus nearly optimal for the deterministic relaxation, with high probability.
--
--   **Formalization Note** With $\eta=2$, $n^{\eta-1}=n$. The lemma is stated under Proposition 1's tuning. This tuning implies the standing conditions of p. 28, and the proofs of Lemmas 4 and 5 need $\tau_n=O(u_n)$, which it also gives. The constants may depend on $x$, $T$, the class parameters and the tuning constants.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 29 (PDF 31), Lemma 3, eqs. (A-4), (A-5)

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_BaselineAssumptions
import Definitions.Def_BesbesZeevi_Nonparametric_Model
import Definitions.Def_BesbesZeevi_Nonparametric_Algorithm

open MeasureTheory ProbabilityTheory ProcessingNetworks.Stability

namespace BesbesZeevi.Nonparametric

/-- Lemma 3, p. 29 (with `η = 2`, so `n^{η-1} = n`): under the tuning of Proposition 1,
`P{r(λ(p^D)) - r(λ(p̂)) > C₁ u_n} ≤ C₃/n^{η-1}` (A-4) and `P{|p̂^c - p^c| > C₂ u_n} ≤ C₃/n^{η-1}`
(A-5), with constants independent of `λ ∈ 𝓛` and `n`. -/
theorem lemma3_price_estimate (P : PriceSet) (L : DemandClass) (x T : ℝ) (hx : 0 < x) (hT : 0 < T)
    (c c' : ℝ) (τ : ℕ → ℝ) (κ : ℕ → ℕ) (htune : Tuning T c c' τ κ) :
    ∃ C₁ C₂ C₃ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧
      ∀ (Ω : Type*) [MeasureSpace Ω] (N : ℝ → Ω → ℕ), IsPoissonProcess N 1 →
      ∀ lam : ℝ → ℝ, L.Mem P lam →
        ∀ pU pC : ℝ, pU ∈ Set.Icc P.pl P.pu →
          IsMaxOn (fun p => p * lam p) (Set.Icc P.pl P.pu) pU →
          pC ∈ Set.Icc P.pl P.pu →
          IsMinOn (fun p => |lam p - x / T|) (Set.Icc P.pl P.pu) pC →
        ∀ n : ℕ, 1 ≤ n →
          ℙ {ω | max pU pC * lam (max pU pC)
                  - phat P lam x T n (τ n) (κ n) N ω * lam (phat P lam x T n (τ n) (κ n) N ω) > C₁ * uSeq n (τ n) (κ n)}
              ≤ ENNReal.ofReal (C₃ / (n : ℝ)) ∧
          ℙ {ω | |phatC P lam x T n (τ n) (κ n) N ω - pC| > C₂ * uSeq n (τ n) (κ n)}
              ≤ ENNReal.ofReal (C₃ / (n : ℝ)) := by sorry

end BesbesZeevi.Nonparametric
