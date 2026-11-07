-- Prove2me | Theorems.Thm_DSICHardRev_lemma_3_5
-- name    : DSICHardRev.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:36:04.092908+00:00
-- url     : https://prove2.me/theorems/2b628e36-6084-4af8-b69e-0344e95b90a6
-- title:
--   Lemma 3.5 — welfare of any allocation on a GS/XOS KSSHD instance is at most $17m/\eta+2\sum_k|S_{i_k}\cap A_k|$
-- statement:
--   Let $\mathcal H$ be an $(\alpha,\eta,\lambda,C,\mathcal U)$-KSSHD on $m$ items for GS or XOS valuations. For every instance drawn from $\mathcal H$ and every allocation $(S_1,\dots,S_n)$,
--   $$\sum_{i\in[n]}v_i(S_i)\;\le\;\frac{17m}{\eta}+2\sum_{k\in[\kappa]}|S_{i_k}\cap A_k|,$$
--   where $i_k\in N_k$ is the bidder with high value for $A_k$.
--
--   Good allocations must therefore give a large part of each $A_k$ to its high-value bidder $i_k$.
--
--   Differences from the source:
--   - encoding: an instance drawn from the KSSHD → any valid sample (j, ϑ, φ) in the support; reason: the support of the distribution of Properties (5)–(12)
--   - reading: all relevant quantities are integers (p.7) → α, η, λ, β = m/η, κ = m/(2α) natural numbers with β·η = m and κ·(2α) = m; reason: the paper's standing integrality convention
--   - encoding: the distribution of Properties (5)–(12) → the uniform law on valid samples (j, ϑ, φ), m ≥ 1, κα + β − α ≤ m; reason: the same law (every choice of A, B admits the same number of bijections); m ≥ 1 excludes the empty auction with no groups, and the size condition is exactly that the sets of Property (7) exist
--   - reading: u_x is either (a) or (b) for each x → one branch (GS, XOS or general) for all x; reason: a KSSHD "using GS valuations" / "for general valuations" is how the paper uses the definition
--   - reading: GS valuations (not defined in the paper) → Kelso–Crawford gross substitutes at all real price vectors (published GrossSubstitutesOn v Set.univ); reason: the standard definition; requiring all real prices is the more restrictive class
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), §3.2, p.14, Lemma 3.5

import Mathlib
import Definitions.Def_DSICHardRev_KSSHD

namespace DSICHardRev

/-- **Lemma 3.5** (F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…), §3.2, p.14):
for any allocation `(S_1, …, S_n)` on an instance drawn from an `(α, η, λ, C, U)`-KSSHD for GS or
XOS valuations, `∑_i v_i(S_i) ≤ 17m/η + 2 ∑_k |S_{i_k} ∩ A_k|`.

**Formalization Note.** "An instance drawn from" the KSSHD is any valid sample `ω` (the support of
the distribution); `i_k = (k, j k ϑ)` is the bidder of group `k` with `x_{i_k, ϑ} = 1`. -/
theorem lemma_3_5 {m : ℕ} (H : KSSHD m) (hb : H.branch = .gs ∨ H.branch = .xos)
    (ω : H.Sample) (hω : H.Valid ω) (S : H.Bidder → Finset (Fin m))
    (hS : Pairwise fun a b => Disjoint (S a) (S b)) :
    ∑ b, H.val ω b (S b) ≤
      17 * (m : ℝ) / H.η + 2 * ∑ k, ((S (H.ik ω k) ∩ H.A ω k).card : ℝ) := by sorry

end DSICHardRev
