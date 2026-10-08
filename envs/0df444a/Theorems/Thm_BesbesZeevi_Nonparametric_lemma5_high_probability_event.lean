-- Prove2me | Theorems.Thm_BesbesZeevi_Nonparametric_lemma5_high_probability_event
-- name    : BesbesZeevi.Nonparametric.lemma5_high_probability_event
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:50:57.638982+00:00
-- url     : https://prove2.me/theorems/8fe58549-f2c9-45bb-a3b5-7fac23afc3f2
-- title:
--   Lemma 5: if $\lambda(\overline p)>x/T$ then $\mathbb P(\mathcal A)\ge1-C_{10}/n^{\eta-1}$
-- statement:
--   Use the tuning of Proposition 1, with $\eta=2$. There are constants $C_2,C_9,C_{10}>0$, independent of the demand function and of $n$, with the following property.
--
--   Let $\lambda\in\mathcal L$ with $\lambda(\overline p)>x/T$ (Case 2 of the proof of Proposition 1). Let $p^u$ and $p^c$ be as in Lemma 1, and put $p^D=\max\{p^u,p^c\}$. Define the event
--
--   $$
--   \mathcal A=\Big\{\min\big\{Y^{(P)}_n,(\lfloor nx\rfloor-Y^{(L)}_n)^+\big\}\ge nx-C_9\,n\,u_n,\ \ |\hat p-p^D|\le C_2u_n\Big\}.
--   $$
--
--   Then for all $n\ge1$,
--
--   $$
--   \mathbb P(\mathcal A)\ \ge\ 1-\frac{C_{10}}{n^{\eta-1}}.
--   $$
--
--   With high probability, the pricing phase therefore sells nearly the whole inventory at a price close to $p^D$.
--
--   **Formalization Note** The printed definition of $\mathcal A$ has $nx-C_9u_n$. The proof (p. 30, (A-13), and p. 43) uses $nx-C_9nu_n$, so the corrected form is stated. The paper's $C_2$ is Lemma 3's constant; here it is existentially quantified together with $C_9$ and $C_{10}$. The inventory in $(\cdot)^+$ is $\lfloor nx\rfloor$ units.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 30 (PDF 32), Lemma 5, eq. (A-12); proof p. 43 (PDF 45)

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_BaselineAssumptions
import Definitions.Def_BesbesZeevi_Nonparametric_Model
import Definitions.Def_BesbesZeevi_Nonparametric_Algorithm

open MeasureTheory ProbabilityTheory ProcessingNetworks.Stability

namespace BesbesZeevi.Nonparametric

/-- Lemma 5, p. 30 (Case 2 of Step 3, `λ(p̄) > x/T`; `η = 2`): the event
`𝒜 = {min{Y^{(P)}_n, (⌊n x⌋ - Y^{(L)}_n)^+} ≥ n x - C₉ n u_n, |p̂ - p^D| ≤ C₂ u_n}` has
`P(𝒜) ≥ 1 - C₁₀/n^{η-1}`. The printed `C₉ u_n` is read as `C₉ n u_n`, as in the proof. -/
theorem lemma5_high_probability_event (P : PriceSet) (L : DemandClass) (x T : ℝ) (hx : 0 < x) (hT : 0 < T)
    (c c' : ℝ) (τ : ℕ → ℝ) (κ : ℕ → ℕ) (htune : Tuning T c c' τ κ) :
    ∃ C₂ C₉ C₁₀ : ℝ, 0 < C₂ ∧ 0 < C₉ ∧ 0 < C₁₀ ∧
      ∀ (Ω : Type*) [MeasureSpace Ω] (N : ℝ → Ω → ℕ), IsPoissonProcess N 1 →
      ∀ lam : ℝ → ℝ, L.Mem P lam → x / T < lam P.pu →
        ∀ pU pC : ℝ, pU ∈ Set.Icc P.pl P.pu →
          IsMaxOn (fun p => p * lam p) (Set.Icc P.pl P.pu) pU →
          pC ∈ Set.Icc P.pl P.pu →
          IsMinOn (fun p => |lam p - x / T|) (Set.Icc P.pl P.pu) pC →
        ∀ n : ℕ, 1 ≤ n →
          ENNReal.ofReal (1 - C₁₀ / (n : ℝ)) ≤
            ℙ {ω | (n : ℝ) * x - C₉ * (n : ℝ) * uSeq n (τ n) (κ n) ≤
                    min (((requestsTotal P lam x T n (τ n) (κ n) N ω : ℕ) : ℝ)
                          - ((requestsLearn P lam n (τ n) (κ n) N ω : ℕ) : ℝ))
                      (max ((salesCap n x : ℝ)
                          - ((requestsLearn P lam n (τ n) (κ n) N ω : ℕ) : ℝ)) 0) ∧
                  |phat P lam x T n (τ n) (κ n) N ω - max pU pC| ≤ C₂ * uSeq n (τ n) (κ n)} := by sorry

end BesbesZeevi.Nonparametric
