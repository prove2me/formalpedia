-- Prove2me | Theorems.Thm_ElimAgree_eq_3_1_disj
-- name    : ElimAgree.eq_3_1_disj
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:36:39.652412+00:00
-- url     : https://prove2.me/theorems/69cd97a6-aeaf-464d-981f-fea5db7d3d48
-- title:
--   Proof of Theorem 3.8 — hypothesis (3.1) for $\mathrm{Elim}(\mathrm{DISJ}_n^k)$ with $\eta=16/\ell$
-- statement:
--   Let $n\ge3$, $k\ge1$, $\ell=\lfloor(n+1)/4\rfloor$ and $N=4\ell-1\le n$. Restrict all instances to the first $N$ elements, let $\nu_z=\mu_\sigma$ with $\sigma_i=D$ if $z_i=1$ and $I$ otherwise, and $\lambda=\mu_D^{\otimes k}=\nu_{(1,\dots,1)}$. Then:
--   1. each $\nu_z$ is a law on pairs of $k$-tuples of subsets of $[n]$;
--   2. $\nu_z$ is supported on $F^{-1}(z)$, where $F=(\mathrm{DISJ}_n,\dots,\mathrm{DISJ}_n)$;
--   3. for every $z$ and every rectangle $A\times B$ of the input space,
--   $$\nu_z(A\times B)\ge\lambda(A\times B)-\frac{16}{\ell}J_\lambda(A\times B),$$
--   which is (3.1) with $\eta=16/\ell$.
--
--   With Theorem 3.1 this gives the lower bounds of Theorem 3.8.
--
--   Differences from the source:
--   - reading: the paragraph's claim that ν_z satisfy (3.1) and can be fed to Theorem 3.1 → three conjuncts: each ν_z is a law, is supported on F^{-1}(z), and satisfies (3.1) with η = 16/ℓ; reason: these are exactly the hypotheses of Theorem 3.1 that the paragraph applies
--   - encoding: restriction of all instances to the first N elements → pushforward of µ_σ along the inclusion Fin N ⊆ Fin n; rectangles of arbitrary tuples of subsets of [n]; reason: the laws vanish off the image; same masses on every rectangle
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), proof of Theorem 3.8, p.10 (PDF p.12), first paragraph

import Mathlib
import Definitions.Def_ElimAgree_IsLaw
import Definitions.Def_ElimAgree_deficit
import Definitions.Def_ElimAgree_nuDisj

namespace ElimAgree

/-- Hypothesis (3.1) for `Elim(DISJ_n^k)` with `η = 16/ℓ` (proof of Theorem 3.8, p.10, first
paragraph), Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*, manuscript (STOC 2027 submission): for `n ≥ 3`, `k ≥ 1` and `ℓ = ⌊(n + 1)/4⌋`, restrict all instances to the
first `N = 4ℓ − 1 ≤ n` elements, let `ν_z = µ_σ` with `σ_i = D` iff `z_i = 1`, and
`λ = µ_D^{⊗k} = ν_{(1,…,1)}`. Then each `ν_z` is a law supported on `F^{−1}(z)` for
`F = (DISJ_n, …, DISJ_n)`, and every rectangle `A × B` of the input space satisfies
`ν_z(A × B) ≥ λ(A × B) − (16/ℓ) J_λ(A × B)`.

**Formalization Note.** `ν_z` is `nuDisj n k z`, the pushforward of `µ_z` along `[N] ⊆ [n]`;
rectangles range over all tuples of subsets of `[n]`. -/
theorem eq_3_1_disj (n k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k) :
    (∀ z : Fin k → Bool, IsLaw (nuDisj n k z)) ∧
    (∀ (z : Fin k → Bool) (p : Inp n k × Inp n k), nuDisj n k z p ≠ 0 → disjAns p.1 p.2 = z) ∧
    (∀ (z : Fin k → Bool) (A B : Finset (Inp n k)),
      lawRect (nuDisj n k z) A B ≥
        lawRect (nuDisj n k (fun _ => true)) A B -
          16 / (ell n : ℝ) * deficit (nuDisj n k (fun _ => true)) A B) := by sorry

end ElimAgree
