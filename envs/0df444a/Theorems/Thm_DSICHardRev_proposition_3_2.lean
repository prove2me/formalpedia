-- Prove2me | Theorems.Thm_DSICHardRev_proposition_3_2
-- name    : DSICHardRev.proposition_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:35:34.006756+00:00
-- url     : https://prove2.me/theorems/b437a71a-3f62-4644-9e5c-ab9dcf14cc67
-- title:
--   Proposition 3.2 — a KSSHD with GS valuations for $\alpha=(m/\gamma)^{2/7}\gamma$, $\eta=(m/\gamma)^{1/7}$, $\lambda=2^\gamma$
-- statement:
--   There is $m_0$ such that for every $m\ge m_0$ and every $\gamma\in[\log m,\,m/10^{10}]$ there exists an $(\alpha,\eta,\lambda,C,\mathcal U)$-KSSHD on $m$ items using GS valuations with parameters
--   $$\alpha=(m/\gamma)^{2/7}\gamma,\qquad \eta=(m/\gamma)^{1/7},\qquad \lambda=2^\gamma,$$
--   whenever these quantities, $m/\eta$ and $m/(2\alpha)$ are integers.
--
--   This is the GS instance of the hard distribution; combined with Theorems 3.7 and 4.5 it yields Theorem 1.1.
--
--   **Formalization Note** "$m$ sufficiently large" (p.12) is the threshold $m_0$. The integrality convention of p.7 is explicit: $\gamma,\alpha,\eta$ are natural numbers equal to the printed expressions, $\eta\mid m$ and $2\alpha\mid m$.
--
--   Differences from the source:
--   - reading: m sufficiently large → ∃ m₀, ∀ m ≥ m₀; reason: the formal content of the paper's "letting m be sufficiently large" (p.12)
--   - reading: all relevant quantities are integers (p.7) → γ, α, η natural numbers equal to the printed expressions, η ∣ m and 2α ∣ m; reason: λ = 2^γ and b = 10γ must be integers, which forces γ ∈ ℕ; β = m/η and κ = m/(2α) must be integers
--   - reading: GS valuations (not defined in the paper) → Kelso–Crawford gross substitutes at all real price vectors (published GrossSubstitutesOn v Set.univ); reason: the standard definition; requiring all real prices is the more restrictive class
--   - encoding: the distribution of Properties (5)–(12) → the uniform law on valid samples (j, ϑ, φ), m ≥ 1, κα + β − α ≤ m; reason: the same law (every choice of A, B admits the same number of bijections); m ≥ 1 excludes the empty auction with no groups, and the size condition is exactly that the sets of Property (7) exist
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), §3.1, p.12, Proposition 3.2 (and the preceding paragraph)

import Mathlib
import Definitions.Def_DSICHardRev_KSSHD

namespace DSICHardRev

/-- **Proposition 3.2** (F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…), §3.1, p.12):
for `γ ∈ [log m, m/10^{10}]` there exists an `(α, η, λ, C, U)`-KSSHD using GS valuations for
parameters `α = (m/γ)^{2/7} γ`, `η = (m/γ)^{1/7}`, `λ = 2^γ` (with `m` sufficiently large, p.12).

**Formalization Note.** "`m` sufficiently large" is `∃ m₀, ∀ m ≥ m₀`. The paper's integrality
convention (p.7) is made explicit: `γ`, `α` and `η` are natural numbers equal to the printed
expressions, and `η ∣ m`, `2α ∣ m` (so that `β = m/η` and `κ = m/(2α)` are integers). -/
theorem proposition_3_2 :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ γ : ℕ, Real.logb 2 m ≤ γ → (γ : ℝ) ≤ (m : ℝ) / 10 ^ 10 →
      ∀ α η : ℕ, (α : ℝ) = ((m : ℝ) / γ) ^ ((2 : ℝ) / 7) * γ →
        (η : ℝ) = ((m : ℝ) / γ) ^ ((1 : ℝ) / 7) → η ∣ m → 2 * α ∣ m →
        ∃ H : KSSHD m, H.branch = .gs ∧ H.α = α ∧ H.η = η ∧ H.lam = 2 ^ γ := by sorry

end DSICHardRev
