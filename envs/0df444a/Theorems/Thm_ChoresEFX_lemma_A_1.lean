-- Prove2me | Theorems.Thm_ChoresEFX_lemma_A_1
-- name    : ChoresEFX.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:10:22.032209+00:00
-- url     : https://prove2.me/theorems/0bda3371-a430-4a35-9f76-4a39261b8ee3
-- title:
--   Lemma A.1 — approximation-factor budgets: $\Lambda_1(t)\le3+20t$ and $\Lambda_k(t)\le2+1/k+8t$
-- statement:
--   Let $k\ge1$. The packet decomposition of a rounded allocation from a capped-price structure with the parameters of display (9) satisfies the hypotheses of Lemma 3.6 with $\lambda=\Lambda_k(t)$ and $\rho=\rho_k(t)$, where
--
--   $$\Lambda_1(t)=\frac{(1+t)(3/2+2t)}{1/2-2t},\qquad \Lambda_k(t)=(1+t)\left(1+\frac{1+t}{\rho}\right)\quad(k\ge2).$$
--
--   For $0<t\le1/100$, $\Lambda_1(t)\le3+20t$, and $\Lambda_k(t)\le2+1/k+8t$ for $k\ge2$.
--
--   These are the constants that fix the approximation factors of the main theorem.
--
--   Differences from the source:
--   - reading: the decomposition in Lemma 3.5 → any packet decomposition of any rounded allocation from any capped-price structure with these parameters; reason: the strongest reading of an unnamed object of the same section
--   - generalization: n ≥ 2 agents (standing, §2, p.5) → any finite agent type; reason: the argument does not use n ≥ 2, and the statement specializes to n ≥ 2
--   - reading: the rounded allocation Y returned by Algorithm 3 → every sort order with the printed tie rule and every admissible matching; reason: the strongest reading of an algorithm with free choices (paper.md decision 8)
--   - encoding: dummy chores and a perfect matching of the chore-slot support graph (Algorithm 3) → an injective map on real chores along positive shares that covers every full slot; reason: equivalent over all dummy placements (paper.md decision 9)
--   - reading: the MPB ratios γ_i of Definition 2.3 (γ_i = min_g Ĉ_i(g)/p_g, p.5) → γ is data of the structure, constrained by (3) and (4); reason: Definition 2.3 lists (3) as a condition, so γ can be read as data; this is the more general reading of the hypothesis, and the MPB ratio satisfies it
-- source:
--   Qin, Fang, Li, Liu, Chen, Polynomial-Time Approximate EFX for Chores via Flow and Matching, STOC 2027 submission (manuscript sha256 b26d14cf…), Lemma A.1, p.19

import Mathlib
import Definitions.Def_ChoresEFX_IsAdmissibleMatching
import Definitions.Def_ChoresEFX_AprRun
import Definitions.Def_ChoresEFX_Lambda

namespace ChoresEFX

/-- **Lemma A.1 (Approximation-factor budgets)**, p.19.

Qin, Fang, Li, Liu, Chen, *Polynomial-Time Approximate EFX for Chores via Flow and Matching*, STOC 2027
submission (manuscript sha256 b26d14cf…).

The decomposition in Lemma 3.5 satisfies the hypotheses of Lemma 3.6 with `λ = Λ_k(t)`. For `0 < t ≤ 1/100`,
`Λ_1(t) ≤ 3 + 20t` and `Λ_k(t) ≤ 2 + 1/k + 8t` for `k ≥ 2`.

**Formalization Note.** "The decomposition in Lemma 3.5" is any packet decomposition of any rounded allocation
from any capped-price structure with the parameters of display (9). `AprHypotheses` contains `λ ≥ 2` and `ρ > 0`. -/
theorem lemma_A_1 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] :
    (∀ (k : ℕ) (_ : 1 ≤ k) (C : ι → κ → ℝ) (t : ℝ) (p : κ → ℝ) (γ : ι → ℝ) (w : ι → κ → ℝ)
      (_ : IsCappedPriceStructure C t (betaParam k t) p γ w) (o : ι → κ → ℕ)
      (_ : IsSortedOrder (betaParam k t) p o) (π : κ → Σ i, Fin (numSlots w i))
      (_ : IsAdmissibleMatching w o π) (S : ι → Finset κ) (K : ι → List (Finset κ))
      (_ : ∀ i,
        IsAgentPacketDecomp k (betaParam k t) (rhoParam k t) p (ssrBundle π i) (S i) (K i)),
      AprHypotheses C p γ k (Lambda k t) (rhoParam k t) S K) ∧
    (∀ t : ℝ, 0 < t → t ≤ 1 / 100 → Lambda 1 t ≤ 3 + 20 * t) ∧
    (∀ (k : ℕ) (t : ℝ), 2 ≤ k → 0 < t → t ≤ 1 / 100 →
      Lambda k t ≤ 2 + 1 / (k : ℝ) + 8 * t) := by sorry

end ChoresEFX
