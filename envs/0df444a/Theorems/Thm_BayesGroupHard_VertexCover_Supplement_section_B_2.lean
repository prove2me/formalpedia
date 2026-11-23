-- Prove2me | Theorems.Thm_BayesGroupHard_VertexCover_Supplement_section_B_2
-- name    : BayesGroupHard.VertexCover.Supplement.section_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:47:32.736577+00:00
-- url     : https://prove2.me/theorems/8cbcaeef-9a30-4258-8213-cc45145b4d80
-- title:
--   §B.2, p. 33 — YES case: φ_i,2 < nℓ̂ + O(1) with ℓ̂ = log(q̄/q̲) < 0, so µ_i,2(1) < exp(−Ω(n))
-- statement:
--   Consider the EXACT-COVER reduction network of Appendix B, with $\bar p=\tfrac12$, $\underline p=\tfrac13$, $\bar p^\star=\tfrac7{12}$, $\underline p^\star=\tfrac7{27}$, $\bar q=\bar p^{1/3}(1-\bar p)^{2/3}$, $\underline q=\underline p^{1/3}(1-\underline p)^{2/3}$ and $\hat\ell=\log(\bar q/\underline q)$.
--
--   1. $\bar q=\tfrac12$.
--   2. If the RXC3 instance $\hat{\mathcal G}_n$ has an exact cover, the number $\hat N$ of exact covers is at least $1$, and the numerator and denominator of (21) are
--   $$\hat N\,\bar p^\star\,\bar q^{\,n}+(1-\bar p^\star)\,\bar p^{\,n}\qquad\text{and}\qquad \hat N\,\underline p^\star\,\underline q^{\,n}+(1-\underline p^\star)\,\underline p^{\,n};$$
--   on every profile realising (19), $\mu_{i,2}(1)=e^{\phi_{i,2}}/(1+e^{\phi_{i,2}})$.
--   3. $\hat\ell<0$.
--   4. There is a constant $C$, independent of $n$ and of the instance, such that on every YES instance and every profile realising (19)
--   $$\phi_{i,2}<n\hat\ell+C .$$
--   5. There are constants $c>0$ and $N$ such that $\mu_{i,2}(1)<e^{-cn}$ on every YES instance with $n\ge N$ and every profile realising (19).
--
--   This is the YES half of the belief gap behind Theorem 2: with an exact cover, agent $i$ is almost certain that $\theta=0$.
--
--   **Formalization Note.** $\hat N$ is `coverCount X`; $1-\bar p^\star$ and $1-\underline p^\star$ are written $1-7/12$, $1-7/27$, and $\bar p^{\,n}$, $\underline p^{\,n}$ as $(1/2)^n$, $(1/3)^n$.
--
--   Differences from the source:
--   - reading: φ_i,2 < log(O(N̂ p̄⋆ q̄^n)/(N̂ p̲⋆ q̲^n)) ≤ nℓ̂ + O(1) ≤ −Ω(n) → ∃ C uniform over n and instances with φ_i,2 < nℓ̂ + C, and ∃ c > 0, ∃ N with µ_i,2(1) < exp(−c n) for n ≥ N; reason: the usual meaning of O(1) and Ω(n), constants chosen before the instance; the middle bound of the chain is not stated separately.
--   - reading: P_1{s̄ = s̄′} = p̄⋆ q̄^n, P_0{s̄ = s̄′} = p̲⋆ q̲^n for one exact cover → the closed forms of the two sums of (21); reason: the sums are these contributions over the N̂ covers plus the profile (0,1,…,1).
--   - encoding: agent i receives no private signal → a fair-coin signal of i; reason: a non-informative signal changes no posterior.
-- source:
--   Hązła, Jadbabaie, Mossel & Rahimian, Bayesian Decision Making in Groups is Hard, arXiv:1705.04770v4, p. 33, §B.2

import Mathlib
import Definitions.Def_BayesGroupHard_VertexCover_Supplement_Network

namespace BayesGroupHard.VertexCover.Supplement

open Finset

/-- §B.2, p. 33 (YES case): `q̄ = 1/2`; with `N̂ ≥ 1` exact covers the likelihood sums of (21)
are `N̂ p̄⋆ q̄^n + (1-p̄⋆) p̄^n` and `N̂ p̲⋆ q̲^n + (1-p̲⋆) p̲^n`; `µ_i,2(1) = e^φ/(1+e^φ)`;
`ℓ̂ = log(q̄/q̲) < 0`; there is a constant `C`, independent of `n` and of the instance, with
`φ_i,2 < n ℓ̂ + C` on every YES instance; and there are `c > 0`, `N` with `µ_i,2(1) < exp(-c n)`
for every YES instance with `n ≥ N`. -/
theorem section_B_2 :
    qBar = 1 / 2 ∧
    (∀ {n : ℕ} (X : RXC3 n), HasCover X →
      1 ≤ coverCount X ∧
      coreMass X true =
        (coverCount X : ℝ) * (7 / 12) * qBar ^ n + (1 - 7 / 12) * (1 / 2) ^ n ∧
      coreMass X false =
        (coverCount X : ℝ) * (7 / 27) * qUnder ^ n + (1 - 7 / 27) * (1 / 3) ^ n ∧
      ∀ s : XAgent n → Bool, Observed X s →
        belief (xcNet X) 2 observer s true =
          Real.exp (rLog (xcNet X) 2 observer s) /
            (1 + Real.exp (rLog (xcNet X) 2 observer s))) ∧
    ellHat < 0 ∧
    (∃ C : ℝ, ∀ {n : ℕ} (X : RXC3 n), HasCover X →
      ∀ s : XAgent n → Bool, Observed X s →
        rLog (xcNet X) 2 observer s < (n : ℝ) * ellHat + C) ∧
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ X : RXC3 n, HasCover X →
      ∀ s : XAgent n → Bool, Observed X s →
        belief (xcNet X) 2 observer s true < Real.exp (-c * n) := by sorry

end BayesGroupHard.VertexCover.Supplement
