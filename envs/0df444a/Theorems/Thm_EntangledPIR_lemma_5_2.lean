-- Prove2me | Theorems.Thm_EntangledPIR_lemma_5_2
-- name    : EntangledPIR.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:11:32.738329+00:00
-- url     : https://prove2.me/theorems/26a45c9d-b3d3-43c4-af90-b7308cf42b5b
-- title:
--   Lemma 5.2 — locally random queries
-- statement:
--   Let $x\in\{0,1\}^n$, and let $y_1,\dots,y_k$ be the queries $y_i=p(\alpha_i)$ of the random curve $p(z)=x+r_1z+\dots+r_\lambda z^\lambda$.
--
--   1. For every set $S\subseteq[k]$ with $|S|\le\lambda$, the tuple $(y_i)_{i\in S}$ is uniformly distributed on $(\mathbb F^n)^S$ over the choice of $r_1,\dots,r_\lambda$.
--   2. For every database $F$ and every choice of $r_1,\dots,r_\lambda$,
--   $$F(x)=F_1(y_1)\oplus\dots\oplus F_k(y_k).$$
--
--   The first part says that at most $\lambda$ queries reveal nothing about the index; the second is the reconstruction from the XOR of the tables' values.
--
--   Differences from the source:
--   - encoding: $\{0,1\}^d$ and $\oplus$ → `Fin d → Bool` and coordinatewise `xor`; reason: Lean convention; same strings
--   - encoding: $\mathbb F_{2^w}$ with any fixed basis containing 1 (p.24) → the concrete field of App. C.2: first irreducible polynomial, polynomial basis, Fermat inverse, $\alpha_i$ the binary representation of $i$; reason: App. C.2 fixes this choice for the client; the multilinear extension is given by the standard formula of p.57
--   - encoding: the tuple is uniformly distributed → every target has exactly $(2^d)^{\lambda-|S|}$ preimages among $(r_1,\dots,r_\lambda)$; reason: uniformity as a count on the finite set; $S=\emptyset$ and $|S|=\lambda$ are included
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), Lemma 5.2, p.24

import Definitions.Def_EntangledPIR_table

namespace EntangledPIR

/-- **Lemma 5.2 (Locally Random Queries)**, Mantri, manuscript (Nov. 2026), p.24. Let `x ∈ {0,1}^n`, with the
queries `y_1, …, y_k` of (5.2). (i) For every set `S ⊆ [k]` with `|S| ≤ λ`, the tuple `(y_i)_{i∈S}` is uniform
on `(F^n)^S` over the choice of `r_1, …, r_λ`: every value `z|_S` has exactly `(2^d)^{λ−|S|}` preimages. (ii) For
every database and every choice of `r_1, …, r_λ`, `F(x) = F_1(y_1) ⊕ ⋯ ⊕ F_k(y_k)`, (5.4). -/
theorem lemma_5_2 {n m : ℕ} (lam : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hlam : 1 ≤ lam) (x : Bits n) :
    (∀ (S : Finset (Fin (shareCount n lam))), S.card ≤ lam →
      ∀ z : Fin (shareCount n lam) → Bits (queryLen n lam),
        (Finset.univ.filter fun r : Fin lam → Bits (queryLen n lam) =>
          ∀ i ∈ S, queries lam x r i = z i).card = (2 ^ queryLen n lam) ^ (lam - S.card)) ∧
    (∀ (F : Bits n → Bits m) (r : Fin lam → Bits (queryLen n lam)),
      F x = bigXor Finset.univ fun i => table lam F i (queries lam x r i)) := by sorry

end EntangledPIR
