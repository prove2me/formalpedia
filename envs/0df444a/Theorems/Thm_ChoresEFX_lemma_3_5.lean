-- Prove2me | Theorems.Thm_ChoresEFX_lemma_3_5
-- name    : ChoresEFX.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:08:52.78639+00:00
-- url     : https://prove2.me/theorems/26901b17-4c84-4f27-bb0a-e992506a7880
-- title:
--   Lemma 3.5 — residual-bundle budgets and Table 1
-- statement:
--   Let $k\ge1$, with the parameters of display (9), $Y$ a rounded allocation from a capped-price structure $(p,\gamma,w)$ for $\hat C$, and $(S,K)$ a packet decomposition of $Y$, which exists. Then residual bundles and packets partition the chores, $Y_i=S_i\cup\bigcup_\ell K_{i,\ell}$, $\nu_i\le2$, and:
--
--   1. each packet contains at most $k$ chores and has price greater than $\rho$;
--   2. if $\nu_i=0$ then $p(S_i)\ge\rho$;
--   3. $p(S_i)$ is at most the entry of Table 1 for $(k,\nu_i)$;
--   4. $\hat C_i(S_i)\le(1+t)\gamma_i$ times that entry.
--
--   Table 1 has the entries $U+\beta,\ U,\ U-\beta$ for $k=1$ and $U+\rho,\ U,\ U-k\beta$ for $k\ge2$, for $\nu_i=0,1,2$.
--
--   These are the budgets that the reallocation lemma consumes.
--
--   Differences from the source:
--   - reading: by Proposition 2.2(1), these bounds imply the corresponding upper bounds on the cost → the explicit bound with factor a = 1 + t, and ν ≤ 2 and the partition as stated clauses; reason: the page speaks of corresponding bounds, and the next section spells out the factor (p.13); p.11 fixes ν and the partition by definition
--   - encoding: Y_i = S_i ⊔ K_{i,1} ⊔ … ⊔ K_{i,ν_i} → a list of packets per agent, with ν_i its length; reason: a Lean convention; same decompositions
--   - generalization: n ≥ 2 agents (standing, §2, p.5) → any finite agent type; reason: the argument does not use n ≥ 2, and the statement specializes to n ≥ 2
--   - reading: the decomposition of Y returned by Algorithm 3 and §3.2 → a decomposition exists, and the bounds hold for every sort order, every admissible matching and every choice among price ties; reason: the strongest reading of an algorithm with free choices (paper.md decision 8)
--   - encoding: dummy chores and a perfect matching of the chore-slot support graph (Algorithm 3) → an injective map on real chores along positive shares that covers every full slot; reason: equivalent over all dummy placements (paper.md decision 9)
--   - reading: the MPB ratios γ_i of Definition 2.3 (γ_i = min_g Ĉ_i(g)/p_g, p.5) → γ is data of the structure, constrained by (3) and (4); reason: Definition 2.3 lists (3) as a condition, so γ can be read as data; this is the more general reading of the hypothesis, and the MPB ratio satisfies it
-- source:
--   Qin, Fang, Li, Liu, Chen, Polynomial-Time Approximate EFX for Chores via Flow and Matching, STOC 2027 submission (manuscript sha256 b26d14cf…), Lemma 3.5 and Table 1, p.11

import Mathlib
import Definitions.Def_ChoresEFX_IsAdmissibleMatching
import Definitions.Def_ChoresEFX_IsPacketDecomp

namespace ChoresEFX

open Finset

/-- **Lemma 3.5 (Residual-bundle budgets)**, with Table 1, p.11.

Qin, Fang, Li, Liu, Chen, *Polynomial-Time Approximate EFX for Chores via Flow and Matching*, STOC 2027
submission (manuscript sha256 b26d14cf…).

Each packet contains at most `k` chores and has price greater than `ρ`. If `ν_i = 0` then `p(S_i) ≥ ρ`. The
upper bounds on `p(S_i)` are those of Table 1, and by Proposition 2.2(1) they imply the corresponding upper
bounds on `Ĉ_i(S_i)`.

**Formalization Note.** For every `k ≥ 1`, with the parameters of display (9), every rounded allocation and
every packet decomposition (a decomposition exists). `ν_i ≤ 2` and the partition `Y_i = S_i ⊔ ⋃ K_{i,ℓ}` come
from the definition on p.11 and are stated, since Lemma 3.6 uses them. The cost bound is
`Ĉ_i(S_i) ≤ a γ_i · (Table 1 entry)` with `a = 1 + t`. -/
theorem lemma_3_5 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (k : ℕ) (hk : 1 ≤ k) (C : ι → κ → ℝ) (t : ℝ) (p : κ → ℝ) (γ : ι → ℝ) (w : ι → κ → ℝ)
    (hs : IsCappedPriceStructure C t (betaParam k t) p γ w) (o : ι → κ → ℕ)
    (ho : IsSortedOrder (betaParam k t) p o) (π : κ → Σ i, Fin (numSlots w i))
    (hπ : IsAdmissibleMatching w o π) :
    (∃ (S : ι → Finset κ) (K : ι → List (Finset κ)), ∀ i,
      IsAgentPacketDecomp k (betaParam k t) (rhoParam k t) p (ssrBundle π i) (S i) (K i)) ∧
    ∀ (S : ι → Finset κ) (K : ι → List (Finset κ)),
      (∀ i, IsAgentPacketDecomp k (betaParam k t) (rhoParam k t) p (ssrBundle π i) (S i) (K i)) →
      IsDecomposition S K ∧
      ∀ i,
        S i ∪ (K i).toFinset.biUnion id = ssrBundle π i ∧
        (K i).length ≤ 2 ∧
        (∀ P ∈ K i, P.card ≤ k ∧ rhoParam k t < priceOf p P) ∧
        (K i = [] → rhoParam k t ≤ priceOf p (S i)) ∧
        priceOf p (S i) ≤
          tableBound k (betaParam k t) (rhoParam k t) (1 + t) (K i).length ∧
        cost C i (S i) ≤ (1 + t) * γ i *
          tableBound k (betaParam k t) (rhoParam k t) (1 + t) (K i).length := by sorry

end ChoresEFX
