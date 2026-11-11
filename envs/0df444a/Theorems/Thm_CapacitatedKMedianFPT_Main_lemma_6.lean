-- Prove2me | Theorems.Thm_CapacitatedKMedianFPT_Main_lemma_6
-- name    : CapacitatedKMedianFPT.Main.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:15:27.310074+00:00
-- url     : https://prove2.me/theorems/ed33bc40-5f48-48c2-b659-646177b294ae
-- title:
--   Lemma 6 — a capacity-respecting assignment to S of cost (1 + 2/e + O(ε))OPT
-- statement:
--   In the setting of Lemma 4, with quotas $\tilde y_{T,i}=\mu_\varepsilon(y_{T,i})$, let $S=\{s_1,\dots,s_k\}$ satisfy $s_i\in F_i$ and $U_{s_i}\ge U_{o^\star_i}$ for all $i\in[k]$, and $v(S)\ge(1-1/e-\varepsilon)\,v(O^\star)$ (the properties guaranteed by Theorem 4). Then there is an assignment $\gamma:C\to S$ such that at most $U_s$ clients are assigned to $s$ for every $s\in S$, and
--   $$\sum_{c\in C}d(c,\gamma(c))\le\Bigl(1+\frac2e+O(\varepsilon)\Bigr)\mathrm{OPT}.$$
--
--   The constant in $O(\varepsilon)$ is absolute. The algorithm need not know $\gamma$: it computes a minimum-cost capacity-respecting assignment to each output set.
--
--   Differences from the source:
--
--   - encoding: O(ε) → C₀·ε with one absolute constant C₀ chosen before all instances; reason: the meaning of O with a universal constant
--   - generalization: the branch fixed by the enumeration: (ℓ, r̃) an entry of L, χ from an k-perfect family, h(c) = argmin with the source's ties → any leaders that are clients, any radii in ℕ, any coloring χ : P → [k], any permutation π and any nearest-leader choice h; reason: the statement uses only these properties; the source's branch is one instance
-- source:
--   Aditya Anand, Yichen Huang, Ragesh Jaiswal, Amit Kumar, Euiwoong Lee, Jatin Yadav, A Tight FPT Approximation for Capacitated k-Median, STOC 2027 submission #1646 (October 2026), p. 14, Lemma 6 and the two properties stated before it; proof p. 14–15

import Mathlib
import Definitions.Def_CapacitatedKMedianFPT_Main_Instance
import Definitions.Def_CapacitatedKMedianFPT_Main_Proxy

set_option autoImplicit false

namespace CapacitatedKMedianFPT.Main

open scoped BigOperators

/-- **Lemma 6** (p. 14). In the branch of Lemma 2 with `o⋆_i ∈ F_i` and quotas
`ỹ_{T,i} = μ_ε(y_{T,i})`, let `S = {s_1, …, s_k}` with `s_i ∈ F_i`, `U_{s_i} ≥ U_{o⋆_i}` and
`v(S) ≥ (1 − 1/e − ε) v(O⋆)`. Then there is an assignment `γ : C → S` with at most `U_s` clients
on every `s ∈ S` and `∑_c d(c, γ(c)) ≤ (1 + 2/e + O(ε)) OPT`, with one absolute constant `C₀`. -/
theorem lemma_6 :
    ∃ C₀ : ℝ, ∀ {P : Type} [Fintype P] [DecidableEq P] (I : Instance P) (ε : ℝ) (G : Guess I)
      (o : Fin I.k → P) (φs : P → P) (s : Fin I.k → P),
      I.IsValid → 0 < ε → ε < 1 / 2 → I.HasIntDistancesUpTo (distanceBound I.size ε) →
      (∀ i, G.ℓ i ∈ I.C) → G.IsNearestLeader →
      I.IsIndexedOptimum o φs → (∀ i, 1 ≤ I.load φs (o i)) →
      ∑ i, (I.load φs (o i) : ℝ) * I.d (o i) (G.ℓ i) ≤ (1 + 2 * ε) * I.cost φs →
      ∑ i, (I.load φs (o i) : ℝ) * (G.r i : ℝ) ≤ (1 + 5 * ε) * I.cost φs →
      (∀ i, o i ∈ G.group i) →
      (∀ i, s i ∈ G.group i) → (∀ i, I.U (o i) ≤ I.U (s i)) →
      (1 - 1 / Real.exp 1 - ε) * G.savings ε (G.roundedQuota ε o φs) (Finset.univ.image o) ≤
        G.savings ε (G.roundedQuota ε o φs) (Finset.univ.image s) →
      ∃ γ : P → P, (∀ c ∈ I.C, γ c ∈ Finset.univ.image s) ∧
        (∀ x ∈ Finset.univ.image s, I.load γ x ≤ I.U x) ∧
        I.cost γ ≤ (1 + 2 / Real.exp 1 + C₀ * ε) * I.cost φs := by sorry

end CapacitatedKMedianFPT.Main
