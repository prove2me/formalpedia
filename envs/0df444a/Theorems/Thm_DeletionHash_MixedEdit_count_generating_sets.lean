-- Prove2me | Theorems.Thm_DeletionHash_MixedEdit_count_generating_sets
-- name    : DeletionHash.MixedEdit.count_generating_sets
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:10.590376+00:00
-- url     : https://prove2.me/theorems/19746cc0-10b8-43b3-a98f-84b01bd97b52
-- title:
--   Lemma 5.1 — count generating sets
-- statement:
--   For every $t\ge2$, $b\ge1$, there is an integer $a_{t,b}\ge1$, independent of $q$. For every finite alphabet of size $q\ge2$, parameters in the standing regime, $x\in W_{n,k}$, and integers $R\ge1$, $0\le c\le2tR$, the number of generating sets $G$ at $R_L(x)$ with $|G|=R$ and $c(G)=c$ satisfies
--   $$\#\{G\}\le n^c q^{6btR}(LR)^{a_{t,b}R}.$$
--   The left side counts underlying finite sets admitting a generating order. It does not count different orders separately. This is the alphabet-uniform count used for all admissible witness sizes.
--
--   Differences from the source:
--   - encoding: the standing assumptions of §§2.2–6 → Regime: q≥2, t≥2, b≥1, k=2 ceil(log_q n)+2, L=3(k+b+1), b<k, L≤n; reason: the section preamble is explicit in each applicable signature
--   - encoding: number of generating sets → extended-natural cardinality of the family of underlying finite sets admitting a generating order; reason: a finite natural upper bound implies finiteness and gives exactly the source count; infinite cardinality cannot default to zero
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), Lemma 5.1, printed p. 16 (PDF p. 18); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf

import Definitions.Def_DeletionHash_MixedEdit_Generation

namespace DeletionHash.MixedEdit

universe u

/-- Lemma 5.1: counts underlying sets admitting an order, without an R! factor. -/
theorem count_generating_sets (t b : ℕ) (ht : 2 ≤ t) (hb : 1 ≤ b) :
    ∃ a : ℕ, 1 ≤ a ∧ ∀ (q : ℕ) (α : Type u) [Fintype α] [DecidableEq α],
      Fintype.card α = q → ∀ n k L : ℕ, Regime q n t b k L →
      ∀ x : Word α n, IsUnique k (letters x) → ∀ R c : ℕ, 1 ≤ R → c ≤ 2*t*R →
      generatingCount k t b (spectrum L (letters x)) R c ≤
        ((n^c * q^(6*b*t*R) * (L*R)^(a*R) : ℕ) : ℕ∞) := by sorry

end DeletionHash.MixedEdit
