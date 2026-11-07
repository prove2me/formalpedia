-- Prove2me | Theorems.Thm_ChoresEFX_display_9
-- name    : ChoresEFX.display_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:09:01.567323+00:00
-- url     : https://prove2.me/theorems/bf08d80d-667e-4378-bc5e-0f7539fc4050
-- title:
--   Display (9) — $p(Y_i)\ge\rho$, $q(Y_i)\le U+\beta$, $|Y_i\cap H|\le k+1$
-- statement:
--   Let $k\ge1$, $\beta=(1+2t)/(k+1)$, $\rho=1-t-\beta$ and $U=1+t$. For every capped-price structure with this cap and every rounded allocation $Y$ from it, every agent $i$ satisfies
--
--   $$p(Y_i)\ge\rho,\qquad q(Y_i)\le U+\beta,\qquad |Y_i\cap H|\le k+1,$$
--
--   where $H=\{g:p_g>\beta\}$.
--
--   These bounds are the input of the packet decomposition.
--
--   Differences from the source:
--   - reading: substituting the parameters from (1), which are printed for k = 1 → β = (1 + 2t)/(k + 1), ρ = 1 − t − β, U = 1 + t for every k ≥ 1; reason: the display has k + 1 and the page speaks of general k; these are the parameters of p.13, and k = 1 gives (1)
--   - generalization: n ≥ 2 agents (standing, §2, p.5) → any finite agent type; reason: the argument does not use n ≥ 2, and the statement specializes to n ≥ 2
--   - reading: the rounded allocation Y returned by Algorithm 3 → every sort order with the printed tie rule and every admissible matching; reason: the strongest reading of an algorithm with free choices (paper.md decision 8)
--   - encoding: dummy chores and a perfect matching of the chore-slot support graph (Algorithm 3) → an injective map on real chores along positive shares that covers every full slot; reason: equivalent over all dummy placements (paper.md decision 9)
--   - reading: the MPB ratios γ_i of Definition 2.3 (γ_i = min_g Ĉ_i(g)/p_g, p.5) → γ is data of the structure, constrained by (3) and (4); reason: Definition 2.3 lists (3) as a condition, so γ can be read as data; this is the more general reading of the hypothesis, and the MPB ratio satisfies it
-- source:
--   Qin, Fang, Li, Liu, Chen, Polynomial-Time Approximate EFX for Chores via Flow and Matching, STOC 2027 submission (manuscript sha256 b26d14cf…), Display (9), p.11

import Mathlib
import Definitions.Def_ChoresEFX_IsAdmissibleMatching

namespace ChoresEFX

open Finset

/-- **Display (9)**, p.11.

Qin, Fang, Li, Liu, Chen, *Polynomial-Time Approximate EFX for Chores via Flow and Matching*, STOC 2027
submission (manuscript sha256 b26d14cf…).

Substituting the parameters from (1) yields `p(Y_i) ≥ ρ`, `q(Y_i) ≤ U + β`, `|Y_i ∩ H| ≤ k + 1`.

**Formalization Note.** Posed for every `k ≥ 1`, with `β = (1 + 2t)/(k + 1)`, `ρ = 1 − t − β`, `U = 1 + t`:
the page states the bound on high-price chores for general `k`, and these are its parameters ("EFkX
Extension", p.13). For `k = 1` they are Eq. (1). -/
theorem display_9 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] (k : ℕ) (hk : 1 ≤ k)
    (C : ι → κ → ℝ) (t : ℝ) (p : κ → ℝ) (γ : ι → ℝ) (w : ι → κ → ℝ)
    (hs : IsCappedPriceStructure C t (betaParam k t) p γ w) (o : ι → κ → ℕ)
    (ho : IsSortedOrder (betaParam k t) p o) (π : κ → Σ i, Fin (numSlots w i))
    (hπ : IsAdmissibleMatching w o π) (i : ι) :
    rhoParam k t ≤ priceOf p (ssrBundle π i) ∧
    priceOf (capped (betaParam k t) p) (ssrBundle π i) ≤ 1 + t + betaParam k t ∧
    ((ssrBundle π i).filter fun g => betaParam k t < p g).card ≤ k + 1 := by sorry

end ChoresEFX
