-- Prove2me | Theorems.Thm_ChoresEFX_lemma_3_2
-- name    : ChoresEFX.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:08:03.817623+00:00
-- url     : https://prove2.me/theorems/5ee68752-6d70-4133-9de4-37c045824770
-- title:
--   Lemma 3.2 — progress from cut updates: $q(C)>(1+t/n)|S|$ and the updated base prices
-- statement:
--   Under the hypotheses of MFCP, let $v>0$ be weights, $s$ a water level, and $f$ a maximum flow of value $F<n$. Let $C$ and $S$ be the sets of chores and agents reachable from $s_0$ in the residual network. Then $C\ne\emptyset$, $S\ne\emptyset$, and
--
--   $$q(C)>(1+t/n)\,|S|.$$
--
--   With the weights of $S$ multiplied by $1+t$, the updated base prices satisfy $r'_g=(1+t)r_g$ for $g\in C$ and $r'_g\ge r_g$ for $g\notin C$.
--
--   This is the progress step behind the iteration bound of MFCP.
--
--   Differences from the source:
--   - generalization: the weights of a round of Algorithm 2 → any positive weights; reason: weights in a run are positive, so the page's case is a special case
--   - encoding: reachable from s0 in the residual network → the least set closed under the source, forward and backward rules, without edges through t0; reason: for a maximum flow t0 is unreachable, so the sets agree
--   - generalization: n ≥ 2 agents (standing, §2, p.5) → n ≥ 1 ([Nonempty ι]); reason: the argument does not use n ≥ 2, and the statement specializes to n ≥ 2
-- source:
--   Qin, Fang, Li, Liu, Chen, Polynomial-Time Approximate EFX for Chores via Flow and Matching, STOC 2027 submission (manuscript sha256 b26d14cf…), Lemma 3.2, p.9

import Mathlib
import Definitions.Def_ChoresEFX_IsMfcpOutput

namespace ChoresEFX

/-- **Lemma 3.2 (Progress from cut updates)**, p.9.

Qin, Fang, Li, Liu, Chen, *Polynomial-Time Approximate EFX for Chores via Flow and Matching*, STOC 2027
submission (manuscript sha256 b26d14cf…).

Suppose `F < n`, and let `C` and `S` be the sets of chores and agents reachable from `s₀` in the residual
network. Then `C ≠ ∅`, `S ≠ ∅`, `q(C) > (1 + t/n)|S|` (4), the updated base prices satisfy
`r'_g = (1 + t) r_g` for `g ∈ C`, and `r'_g ≥ r_g` for `g ∉ C`.

**Formalization Note.** Any positive weights and any maximum flow of value `< n`, which covers every failed
round of every run. -/
theorem lemma_3_2 {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (C : ι → κ → ℝ) (hC : ∀ i g, 0 < C i g) (t β : ℝ) (ht : 0 < t) (ht' : t ≤ 1 / 100)
    (hβ : 0 < β) (hβ' : β < 1) (hmβ : (Fintype.card ι : ℝ) < (Fintype.card κ : ℝ) * β)
    (v : ι → ℝ) (hv : ∀ i, 0 < v i) (s : ℝ) (hs : IsWaterLevel C β v s) (f : ι → κ → ℝ)
    (hf : IsMaximumFlow C t β v s f) (hF : flowValue f < (Fintype.card ι : ℝ)) :
    (reachChores C t β v s f).Nonempty ∧
    (reachAgents C t β v s f).Nonempty ∧
    (1 + t / (Fintype.card ι : ℝ)) * ((reachAgents C t β v s f).card : ℝ) <
      priceOf (capped β (roundPrice C v s)) (reachChores C t β v s f) ∧
    (∀ g ∈ reachChores C t β v s f,
      basePrice C (updatedWeights C t β v s f) g = (1 + t) * basePrice C v g) ∧
    (∀ g, g ∉ reachChores C t β v s f →
      basePrice C v g ≤ basePrice C (updatedWeights C t β v s f) g) := by sorry

end ChoresEFX
