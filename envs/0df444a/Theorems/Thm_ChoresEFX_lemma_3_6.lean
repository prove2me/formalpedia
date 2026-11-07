-- Prove2me | Theorems.Thm_ChoresEFX_lemma_3_6
-- name    : ChoresEFX.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:11:01.982452+00:00
-- url     : https://prove2.me/theorems/03df912f-4953-4e23-9c40-ae42326d4286
-- title:
--   Lemma 3.6 — adaptive packet reallocation returns a complete $\lambda$-EFkX allocation (running-time clause carried by Theorem 1.1)
-- statement:
--   Let $n\ge2$, $k\ge1$, let $\hat C>0$ and $p>0$, and let $\gamma_ip_g\le\hat C_i(g)$. Suppose $\lambda\ge2$; each agent has at most two packets; each packet contains at most $k$ chores and has price at least $\rho>0$; residual bundles and packets partition the chores; and
--
--   $$p(S_i)\ge\rho,\quad\hat C_i(S_i)\le\lambda\gamma_i\rho\quad(\nu_i=0),\qquad\hat C_i(S_i)\le(\lambda-\nu_i)\gamma_i\rho\quad(\nu_i\in\{1,2\}).$$
--
--   Then Algorithm 4 has a run, and every run returns a complete $\lambda$-EFkX allocation.
--
--   The lemma is the step that turns price bounds into fairness against every comparison bundle.
--
--   Differences from the source:
--   - reading: Algorithm 4 runs in O(n²m + nm log m) time → the operation count is not stated here; the goal theorem_1_1 carries the running time on its machine; reason: the procedure takes real-valued data; the count is an arithmetic one (paper.md decision 7)
--   - reading: Algorithm 4 returns a complete allocation → a run exists, and the conclusion holds for every order and every tie; reason: the strongest reading of an algorithm with free choices (paper.md decision 8)
--   - reading: the hypotheses printed in the lemma → also n ≥ 2, Ĉ > 0, p > 0, γ_i p_g ≤ Ĉ_i(g), and that S and the packets partition the chores; reason: the standing conditions: p.5 for n, Algorithm 2 for Ĉ, Definition 2.3 for p, the proof's use of Proposition 2.2(1), and p.11 for the decomposition
-- source:
--   Qin, Fang, Li, Liu, Chen, Polynomial-Time Approximate EFX for Chores via Flow and Matching, STOC 2027 submission (manuscript sha256 b26d14cf…), Lemma 3.6, p.12

import Mathlib
import Definitions.Def_ChoresEFX_AprRun

namespace ChoresEFX

/-- **Lemma 3.6 (Adaptive packet reallocation)** (running-time clause carried by Theorem 1.1), p.12.

Qin, Fang, Li, Liu, Chen, *Polynomial-Time Approximate EFX for Chores via Flow and Matching*, STOC 2027
submission (manuscript sha256 b26d14cf…).

Suppose `λ ≥ 2`, each agent has at most two packets, each packet contains at most `k` chores and has price at
least `ρ > 0`, and (10), (11) hold. Then Algorithm 4 returns a complete `λ`-EFkX allocation.

**Formalization Note.** `n ≥ 2`, because Algorithm 4 needs a bundle `B₁` of another agent (the paper's standing
assumption, p.5). `Ĉ > 0` and `p > 0` are the standing conditions, and `γ_i p_g ≤ Ĉ_i(g)` is Definition 2.3 (3),
which the proof uses ("By Proposition 2.2(1)"). A run exists, and the conclusion holds for every run. The clause
`O(n²m + nm log m)` counts operations on real-valued data and is carried by the goal's machine (paper.md
decision 7). -/
theorem lemma_3_6 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (hn : 2 ≤ Fintype.card ι) (k : ℕ) (hk : 1 ≤ k) (C : ι → κ → ℝ) (hC : ∀ i g, 0 < C i g)
    (p : κ → ℝ) (hp : ∀ g, 0 < p g) (γ : ι → ℝ) (hγ : ∀ i g, γ i * p g ≤ C i g) (lam ρ : ℝ)
    (S : ι → Finset κ) (K : ι → List (Finset κ)) (h : AprHypotheses C p γ k lam ρ S K) :
    (∃ X, AprRun C k lam S K X) ∧
    ∀ X, AprRun C k lam S K X → IsPartition X ∧ IsAlphaEFkX C k lam X := by sorry

end ChoresEFX
