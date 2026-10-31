-- Prove2me | Theorems.Thm_CompetitionComplexity_claim_1
-- name    : CompetitionComplexity.claim_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:23.756887+00:00
-- url     : https://prove2.me/theorems/f2351986-3522-4e17-b3c7-db46d85393e0
-- title:
--   Claim 1 — if $\partial B_{n+1}/\partial B_n\to\rho<1$, then $B_n$ converges to some $\mathcal B>0$
-- statement:
--   Let $(B_n)_{n\in\mathbb N}$ be a real sequence with $B_0=0$ satisfying properties (a)–(c): strictly increasing, non-increasing increments $\partial B_n=B_{n+1}-B_n$, and non-decreasing ratios $\partial B_{n+1}/\partial B_n$. These ratios converge to some $\rho\in(0,1]$. If $\rho<1$, then there is $\mathcal B>0$ with
--   $$
--   \lim_{n\to\infty}B_n=\mathcal B .
--   $$
--   In the construction of Lemma 3 this is what makes the constructed distribution function reach $1$ at a finite point when $\rho<1$.
--
--   **Formalization Note** $\rho$ is introduced as the limit of the ratios; that the limit exists follows from (b)–(c) and is not an extra assumption.
--
--   Differences from the source:
--   - encoding: ρ, the limit of (∂Bₙ₊₁/∂Bₙ) (which exists by (b)–(c)) → a real ρ with the hypothesis that the ratios tend to ρ; reason: names the limit the source refers to; the limit exists for every such B
-- source:
--   Brustle, Correa, Dütting, Verdugo, The Competition Complexity of Dynamic Pricing, accepted manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), doi:10.1287/moor.2022.0230, Claim 1, p.11 (in the proof of Lemma 3)

import Mathlib
import Definitions.Def_CompetitionComplexity_SequenceProperties

open Filter Topology

namespace CompetitionComplexity

/-- **Claim 1** (in the proof of Lemma 3).
Brustle, Correa, Dütting, Verdugo, *The Competition Complexity of Dynamic Pricing*, accepted
manuscript (LSE eprint 124364) of Math. Oper. Res. 49(3) (2024), Claim 1, p.11:
"Suppose that ρ < 1. Then, there exists a value B > 0 such that limn→∞ Bn = B."
Context (same page): "(Bn)n∈N satisfies properties (b)-(c) the sequence (∂Bn+1/∂Bn)n∈N converges
to a value ρ ∈ (0,1]", for a sequence with `B₀ = 0` satisfying (a)–(c) (Lemma 3).

**Formalization Note.** `ρ` is named by the hypothesis that it is the limit of the ratios; the
existence of that limit follows from (b)–(c) and is not an extra assumption. -/
theorem claim_1 (B : ℕ → ℝ) (hB0 : B 0 = 0) (ha : PropA B) (hb : PropB B) (hc : PropC B)
    (ρ : ℝ) (hρ : Tendsto (fun n => dS B (n + 1) / dS B n) atTop (𝓝 ρ)) (hρ1 : ρ < 1) :
    ∃ Bv : ℝ, 0 < Bv ∧ Tendsto B atTop (𝓝 Bv) := by sorry

end CompetitionComplexity
