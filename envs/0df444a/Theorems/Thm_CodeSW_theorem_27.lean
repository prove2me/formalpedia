-- Prove2me | Theorems.Thm_CodeSW_theorem_27
-- name    : CodeSW.theorem_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:23:43.534846+00:00
-- url     : https://prove2.me/theorems/9dfbd868-675b-4a2f-a61d-7bdb22a73116
-- title:
--   Theorem 27 [DS93] (corrected: spectral gap $1-\lambda_2$ for reversible chains)
-- statement:
--   **Comparison of spectral gaps.** Let $P$ and $Q$ be transition matrices on a finite state space $X$ with at least two states, both reversible with respect to the same strictly positive distribution $\pi$, which is the unique stationary distribution of each. Suppose
--   $$P(x,y)\le Q(x,y)\le cP(x,y)\quad\text{for all }x\ne y\in X$$
--   and some $c>0$. Then the spectral gaps $\gamma=1-\lambda_2$, with $\lambda_2$ the largest eigenvalue different from $1$, satisfy
--   $$\gamma(P)\le\gamma(Q)\le c\,\gamma(P).$$
--
--   This is the Diaconis–Saloff-Coste comparison principle, which transfers spectral information between two chains with the same stationary law.
--
--   Differences from the source:
--   - correction: Δ(P) ≤ Δ(Q) ≤ cΔ(P) for Δ = 1 − max{|λ| : λ ≠ 1}, for chains with the same unique fixed point → spectral gap 1 − λ₂, for chains reversible with respect to π; reason: the printed statement is false: on two states P ≡ 1/2 and Q the swap have the unique fixed point (1/2,1/2) and P(x,y) ≤ Q(x,y) ≤ 2P(x,y) for x ≠ y, but Δ(P) = 1 and Δ(Q) = 0. Both chains are reversible, so the gap itself must change; the two gaps coincide for the lazy chains to which the paper applies the theorem
--   - correction: a unique fixed point π → additionally π > 0; reason: without it the statement is false: on {a, b, y} with y absorbing, P rows (.49,.01,.5), (.2,.79,.01), (0,0,1) and Q rows (.1,.4,.5), (.2,.79,.01), (0,0,1) have unique stationary law δ_y, are reversible for it, and P ≤ Q ≤ 40P off the diagonal, but γ(P) ≈ .2035 > γ(Q) ≈ .1089; the setting of [DS93] is irreducible
--   - encoding: a state space X → X has at least two states (Nontrivial X); reason: on one state there is no eigenvalue ≠ 1, both gaps are the junk value 1 − sSup ∅ = 1, and c < 1 would falsify a claim about nothing
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), Theorem 27, p.33

import Definitions.Def_mm_spectral
open Matrix

namespace CodeSW

/-- **Theorem 27 [DS93], corrected.** Let `P` and `Q` be transition matrices on a state space
`X` with at least two states, reversible with respect to the same strictly positive distribution
`π`, which is the unique fixed point of each, and suppose `P(x,y) ≤ Q(x,y) ≤ c P(x,y)` for all
`x ≠ y` and some `c > 0`. Then the spectral gaps `γ = 1 − λ₂` satisfy
`γ(P) ≤ γ(Q) ≤ c γ(P)` (Hangleiter, Ju, Vazirani, *Code Swendsen-Wang Dynamics*,
arXiv:2510.08446, manuscript sha256 4e4abb5e…, Theorem 27, p.33).

**Formalization Note** The page states the conclusion for the absolute gap
`∆ = 1 − max{|λ| : λ ≠ 1}`, which is false (two states, `P ≡ 1/2`, `Q` the swap, `c = 2`:
`∆(P) = 1 > ∆(Q) = 0`). This is the Diaconis–Saloff-Coste comparison for the spectral gap
`MarkovMixing.spectralGap = 1 − λ₂` of reversible chains. Positivity of `π` and `|X| ≥ 2` are
part of the correction (see the item's differences). -/
theorem theorem_27 {X : Type*} [Fintype X] [DecidableEq X] [Nontrivial X]
    (P Q : Matrix X X ℝ) (hP : MarkovMixing.IsStochastic P) (hQ : MarkovMixing.IsStochastic Q)
    (π : X → ℝ) (hπP : MarkovMixing.IsStationary P π) (hπQ : MarkovMixing.IsStationary Q π)
    (huP : ∀ ν : X → ℝ, MarkovMixing.IsStationary P ν → ν = π)
    (huQ : ∀ ν : X → ℝ, MarkovMixing.IsStationary Q ν → ν = π)
    (hπpos : ∀ x, 0 < π x)
    (hrevP : MarkovMixing.DetailedBalance P π) (hrevQ : MarkovMixing.DetailedBalance Q π)
    (c : ℝ) (hc : 0 < c) (hPQ : ∀ x y : X, x ≠ y → P x y ≤ Q x y ∧ Q x y ≤ c * P x y) :
    MarkovMixing.spectralGap P ≤ MarkovMixing.spectralGap Q ∧
      MarkovMixing.spectralGap Q ≤ c * MarkovMixing.spectralGap P := by sorry

end CodeSW
