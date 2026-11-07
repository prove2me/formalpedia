-- Prove2me | Theorems.Thm_ChoresEFX_lemma_B_1
-- name    : ChoresEFX.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:06:22.661035+00:00
-- url     : https://prove2.me/theorems/a523f452-c7c6-45c4-b6b8-a7eaa0fa2334
-- title:
--   Lemma B.1 — block insertion: $R^k_i(B\cup E)\le\max\{1,r/k\}\,c_i(B)$
-- statement:
--   Let the costs be nonnegative and $k\ge1$. Let $B$ be a bundle with at least $k$ chores, and let $E$ be a block of $r$ chores outside $B$, each no more costly to agent $i$ than each chore of $B$. Then
--
--   $$R^k_i(B\cup E)\le\max\{1,r/k\}\,c_i(B).$$
--
--   The lemma bounds the residual cost after a block of cheap chores is inserted into the cheapest bundle, which is the step that drives Algorithm 5.
--
--   Differences from the source:
--   - generalization: every current bundle has at least k chores and B is the bundle cheapest to i; E is cheaper than any assigned chore → only B has at least k chores; E is cheaper than B's chores; B need not be cheapest; reason: the page's situation is a special case and these are the only facts used
--   - generalization: n ≥ 2 agents (standing, §2, p.5) → any agent type (any n); reason: the inequality concerns one agent's costs, and the statement specializes to n ≥ 2
-- source:
--   Qin, Fang, Li, Liu, Chen, Polynomial-Time Approximate EFX for Chores via Flow and Matching, STOC 2027 submission (manuscript sha256 b26d14cf…), Lemma B.1, pp.20–21

import Mathlib
import Definitions.Def_ChoresEFX_IsAlphaEFX

namespace ChoresEFX

/-- **Lemma B.1 (Block insertion)**, pp.20–21.

Qin, Fang, Li, Liu, Chen, *Polynomial-Time Approximate EFX for Chores via Flow and Matching*, STOC 2027
submission (manuscript sha256 b26d14cf…).

If the bundle `B` has at least `k` chores and a new block `E` of `r` chores has each chore no more costly
to `i` than each chore of `B`, then `R^k_i(B ∪ E) ≤ max{1, r/k} c_i(B)`.

**Formalization Note.** The page assumes this of every current bundle and of the cheapest bundle `B`; the
statement uses only `B`, as the proof does. `k ≥ 1` is the paper's standing condition: in Lean `r/0 = 0`. -/
theorem lemma_B_1 {ι κ : Type*} [DecidableEq κ] (c : ι → κ → ℝ) (hc : ∀ i g, 0 ≤ c i g)
    (k : ℕ) (hk : 1 ≤ k) (i : ι) (B E : Finset κ) (hB : k ≤ B.card) (hdisj : Disjoint B E)
    (hE : ∀ e ∈ E, ∀ b ∈ B, c i e ≤ c i b) :
    resid c k i (B ∪ E) ≤ max 1 ((E.card : ℝ) / (k : ℝ)) * cost c i B := by sorry

end ChoresEFX
