-- Prove2me | Theorems.Thm_CongruencyTU_lemma_8
-- name    : CongruencyTU.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:46:51.652987+00:00
-- url     : https://prove2.me/theorems/f47157ec-b993-44f4-b8b9-91ae165352a4
-- title:
--   Lemma 8 (corrected: singleton intervals allowed): a sum in R that cannot be shortened has at most m − |R| terms
-- statement:
--   Let $m\in\mathbb Z_{>0}$, $R\subseteq\{0,\dots,m-1\}$ and $r_1,\dots,r_\ell\in\mathbb Z$ with $\sum_{i\in[\ell]}r_i\in R\pmod m$. If there is no interval $I=\{i_1,\dots,i_2\}$ with $i_1,i_2\in[\ell]$ and $i_1\le i_2$ such that $\sum_{i\in[\ell]\setminus I}r_i\in R\pmod m$, then
--   $$\ell\le m-|R|.$$
--
--   As printed, the lemma requires $i_1<i_2$, which excludes one-element intervals, and is then false: for $m=2$, $R=\{1\}$, $(r_1,r_2)=(1,0)$ the only interval with $i_1<i_2$ is $\{1,2\}$, whose complement has sum $0\notin R$, yet $\ell=2>1=m-|R|$. The paper's own proof removes the singleton interval $\{\ell\}$.
--
--   The lemma bounds how many elementary steps are needed to return to a feasible residue, which is the source of every width bound $m-|R|$ in the paper.
--
--   **Formalization Note** $[\ell]$ is indexed $0,\dots,\ell-1$.
--
--   Differences from the source:
--
--   - correction: intervals I = {i₁, …, i₂} with i₁ < i₂ → intervals with i₁ ≤ i₂ (singletons allowed); reason: as printed the lemma is false: m = 2, R = {1}, (r₁, r₂) = (1, 0) meets the hypothesis but ℓ = 2 > 1 = m − |R|; the paper's proof uses the singleton interval {ℓ}
--   - reading: Σ_{i∈[ℓ]∖I} rᵢ ∈ R → Σ_{i∈[ℓ]∖I} rᵢ ≡ r (mod m) for some r ∈ R; reason: membership in R is modulo m throughout the lemma, as in its first hypothesis and its proof
--   - encoding: indices [ℓ] = {1, …, ℓ} → Fin ℓ = {0, …, ℓ − 1}; reason: Lean indexing; same intervals
-- source:
--   Nägele, Santiago, Zenklusen, Congruency-Constrained TU Problems Beyond the Bimodular Case, arXiv:2109.03148v3 [math.OC] (preprint, 25 Apr 2023), https://arxiv.org/abs/2109.03148v3, p.5 (PDF p.6), Lemma 8

import Mathlib
import Definitions.Def_CongruencyTU_Pattern

namespace CongruencyTU

/-- **Lemma 8** (Nägele–Santiago–Zenklusen, *Congruency-Constrained TU Problems Beyond the Bimodular Case*, arXiv:2109.03148v3 (preprint), p.5, PDF p.6), **corrected**: "Let m ∈ ℤ_{>0}, R ⊆ {0, …, m − 1}, and
r₁, …, r_ℓ ∈ ℤ with Σ_{i∈[ℓ]} rᵢ ∈ R (mod m). If there is no interval I = {i₁, …, i₂} with
i₁, i₂ ∈ [ℓ] and i₁ < i₂ such that Σ_{i∈[ℓ]∖I} rᵢ ∈ R, then ℓ ≤ m − |R|."

As printed (`i₁ < i₂`, no singleton intervals) the lemma is false: `m = 2`, `R = {1}`, `ℓ = 2`,
`(r₁, r₂) = (1, 0)` satisfies the hypothesis (the only interval `{1, 2}` leaves the empty sum
`0 ∉ R`) but `ℓ = 2 > 1 = m − |R|`. The paper's proof uses the singleton interval `{ℓ}`. Stated here
with `i₁ ≤ i₂`.

**Formalization Note.** `[ℓ]` is `Fin ℓ` (0-based); the interval is `{i : i₁ ≤ i ≤ i₂}`. "∈ R" for
the sum over `[ℓ] ∖ I` is read modulo `m`, as for the full sum. -/
theorem lemma_8 (m : ℕ) (hm : 0 < m) (R : Finset ℕ) (hR : ∀ r ∈ R, r < m) (ℓ : ℕ)
    (r : Fin ℓ → ℤ) (hsum : InRes m R (∑ i, r i))
    (hno : ¬ ∃ i₁ i₂ : Fin ℓ, i₁ ≤ i₂ ∧
      InRes m R (∑ i ∈ Finset.univ.filter (fun i => ¬ (i₁ ≤ i ∧ i ≤ i₂)), r i)) :
    ℓ ≤ m - R.card := by sorry

end CongruencyTU
