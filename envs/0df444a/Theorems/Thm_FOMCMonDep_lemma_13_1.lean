-- Prove2me | Theorems.Thm_FOMCMonDep_lemma_13_1
-- name    : FOMCMonDep.lemma_13_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:26:20.444281+00:00
-- url     : https://prove2.me/theorems/383b21c8-b447-432b-bd1d-85169e0d2c0e
-- title:
--   Lemma 13.1 (type tree sizes) — type trees are counted and sized by $|\mathrm{Types}^G_{d,d}|$ of the ball
-- statement:
--   Let $k\ge1$ and $q\in\mathbb N$, and put $r=\rho^+(k,q)$ and $d=r+k+q$. For every partial graph $G$:
--
--   1. $\bigl|\{\mathrm{tree}^G_{k+i,q-i}(\bar v):\bar v\in X^\ell\}\bigr|\le|\mathrm{Types}^G_{d,d}(X)|$ for all $i\in\{0,\dots,q\}$, $\ell\in[k+i]$ and $X\subseteq V(G)$;
--   2. $\|\mathrm{tree}^G_{k,q}(a)\|\le\mathrm{poly}_{k,q}\bigl(|\mathrm{Types}^G_{d,d}(\mathrm{Ball}^G_r(a))|\bigr)$ for every $a\in V(G)$.
--
--   The lemma converts bounds on the number of ordinary types (the depth-$d$ width) into bounds on the number and size of type trees, as needed by the model checking algorithm (Theorem 4.3).
--
--   **Formalization Note** Types are first-order types over the signature of partial graphs without parameters. $\mathrm{poly}_{k,q}(K)$ is $(K+2)^e$ with $e$ chosen after $k,q$.
--
--   Differences from the source:
--   - encoding: type trees and their size ∥τ∥ → the canonical codes treeCode and their lengths treeSize; reason: the paper's canonical representation (p.40); the code determines the tree
--   - encoding: poly_{k,q}(K) → (K + 2)^e with e after k, q; reason: the asymptotic convention of §3, p.11
--   - encoding: a partial graph (finite vertex set, E and N disjoint, a partition into named colors) → PartialGraph n: vertex set Fin n, color : Fin n → ℕ (one color per vertex), E and N disjoint simple graphs; reason: every finite partial graph has a copy on some Fin n; Part III names the colors by a countable set (p.38)
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), Lemma 13.1, p.50 (PDF 52)

import Mathlib
import Definitions.Def_FOMCMonDep_tp
import Definitions.Def_FOMCMonDep_treeCode

set_option autoImplicit false

namespace FOMCMonDep

/-- **Lemma 13.1 (type tree sizes).** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §13, p.50 (PDF 52): "Let k ⩾ 1 and q ∈ N, and put
r := ρ⁺(k, q) and d := r + k + q. The following holds for every partial graph G.
(i) |{tree^G_{k+i,q−i}(v̄) : v̄ ∈ X^ℓ}| ⩽ |Types^G_{d,d}(X)| for all i ∈ {0, . . . , q}, ℓ ∈ [k + i], and X ⊆ V(G).
(ii) ∥tree^G_{k,q}(a)∥ ⩽ poly_{k,q}(|Types^G_{d,d}(Ball^G_r(a))|) for every a ∈ V(G)."

**Formalization Note.** Partial graphs are finite (on `Fin n`); types are first-order types over `PGLang` without
parameters. Type trees are their canonical codes (`treeCode G q k ā`, argument order `q` then `k`), so (i) counts
distinct codes; tuples of length `ℓ` are lists. `poly_{k,q}(K)` is `(K + 2)^e` with `e` after `k, q` (§3, p.11);
`K` is finite (at most `n^d`), so `toNat` is exact. `∥τ∥` is `treeSize`, the length of the code. -/
theorem lemma_13_1 (k q : ℕ) (hk : 1 ≤ k) :
    (∀ (n : ℕ) (G : PartialGraph n) (i ℓ : ℕ), i ≤ q → 1 ≤ ℓ → ℓ ≤ k + i → ∀ X : Set (Fin n),
      ((fun v : List (Fin n) => treeCode G (q - i) (k + i) v) '' {v | v.length = ℓ ∧ ∀ x ∈ v, x ∈ X}).encard ≤
        typeCount G.toStructure (rhoPlus k q + k + q) (rhoPlus k q + k + q) X ∅) ∧
    ∃ e : ℕ, ∀ (n : ℕ) (G : PartialGraph n) (a : Fin n),
      treeSize G k q [a] ≤
        ((typeCount G.toStructure (rhoPlus k q + k + q) (rhoPlus k q + k + q) (G.ball (rhoPlus k q) a) ∅).toNat
          + 2) ^ e := by sorry

end FOMCMonDep
