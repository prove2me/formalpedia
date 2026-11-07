-- Prove2me | Theorems.Thm_ChoresEFX_proposition_2_2
-- name    : ChoresEFX.proposition_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:08:00.961198+00:00
-- url     : https://prove2.me/theorems/9d8e874d-3f37-4925-84f4-3e9cbd8121f8
-- title:
--   Proposition 2.2 — cost and price comparisons on MPB-supported bundles
-- statement:
--   Let $c$ be a positive cost matrix, $p$ a positive price vector, $i$ an agent and $a\ge1$. Let $\gamma_i=\min_g c_i(g)/p_g$. For every bundle $B$ and every $S\subseteq A_i(a)$:
--
--   1. $c_i(B)\ge\gamma_i\,p(B)$ and $c_i(S)\le a\gamma_i\,p(S)$;
--   2. if $p(B)\ge\rho>0$ and $p(S)\le b$, then $c_i(S)\le\frac{ab}{\rho}\,c_i(B)$.
--
--   This translates price bounds into cost bounds throughout the analysis.
--
--   Differences from the source:
--   - encoding: the set of chores M with γ_i a minimum over M → [Nonempty κ] and a real infimum over a finite type; reason: a Lean convention: the minimum needs at least one chore
--   - generalization: n ≥ 2 agents (standing, §2, p.5) → any agent type (any n); reason: the proposition fixes one agent, and the statement specializes to n ≥ 2
-- source:
--   Qin, Fang, Li, Liu, Chen, Polynomial-Time Approximate EFX for Chores via Flow and Matching, STOC 2027 submission (manuscript sha256 b26d14cf…), Proposition 2.2, p.5

import Mathlib
import Definitions.Def_ChoresEFX_IsCappedPriceStructure

namespace ChoresEFX

/-- **Proposition 2.2**, p.5.

Qin, Fang, Li, Liu, Chen, *Polynomial-Time Approximate EFX for Chores via Flow and Matching*, STOC 2027
submission (manuscript sha256 b26d14cf…).

Fix a positive price vector `p` and an agent `i`. For every `B ⊆ M` and `S ⊆ A_i(a)`:
(1) `c_i(B) ≥ γ_i p(B)` and `c_i(S) ≤ a γ_i p(S)`; (2) if `p(B) ≥ ρ > 0` and `p(S) ≤ b`, then
`c_i(S) ≤ (ab/ρ) c_i(B)`.

**Formalization Note.** Positive costs and `a ≥ 1` are the standing conditions of p.5 ("For a positive
additive cost matrix", "For a ≥ 1"). `[Nonempty κ]` makes `γ_i` a real minimum. -/
theorem proposition_2_2 {ι κ : Type*} [Fintype κ] [Nonempty κ] (c : ι → κ → ℝ)
    (hc : ∀ i g, 0 < c i g) (p : κ → ℝ) (hp : ∀ g, 0 < p g) (i : ι) (a : ℝ) (ha : 1 ≤ a)
    (B S : Finset κ) (hS : ∀ g ∈ S, g ∈ mpbSet c p a i) :
    mpbRatio c p i * priceOf p B ≤ cost c i B ∧
    cost c i S ≤ a * mpbRatio c p i * priceOf p S ∧
    ∀ ρ b : ℝ, 0 < ρ → ρ ≤ priceOf p B → priceOf p S ≤ b →
      cost c i S ≤ a * b / ρ * cost c i B := by sorry

end ChoresEFX
