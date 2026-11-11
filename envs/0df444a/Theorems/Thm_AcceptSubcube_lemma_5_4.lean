-- Prove2me | Theorems.Thm_AcceptSubcube_lemma_5_4
-- name    : AcceptSubcube.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:58:40.557808+00:00
-- url     : https://prove2.me/theorems/77c0b00a-31a1-4529-8e05-d1339c33eaa3
-- title:
--   Lemma 5.4 — the additive term $D_j(n)r^j/B$
-- statement:
--   Let $k\ge2$, $0\le t\le k-2$, $\ell=k-t$, $n\ge k$, $\Pi_t=\binom nt$, $D_j(n)=\binom{n-j}{k-j}$, and $c>0$. Let $1\le r\le n$ be an integer and $B>\Pi_t$ real with $r^\ell\le cB/\Pi_t$, and put $u=B/\Pi_t$. Then:
--
--   1. for every $j\le\ell$,
--   $$\frac{D_j(n)\,r^j}{B}\le c^{j/\ell}\,\frac{D_j(n)}{\Pi_t}\,u^{-(\ell-j)/\ell};$$
--   2. $D_\ell(n)\,r^\ell\le c\,B$;
--   3. there is a constant $C$ depending only on $k$ and $c$ such that, whenever $\ell\ge4$, $D_3(n)r^3/B\le C\,n^{\ell-3}u^{-(\ell-3)/\ell}$.
--
--   With $c=c_k$ of Lemma 5.3 this compares the repair's additive term with the optimum.
--
--   Differences from the source:
--   - generalization: c_k of Lemma 5.3 → every constant c > 0; reason: the lemma uses no property of c_k; c = c_k specializes to the source
--   - generalization: B the optimum of the instance → every real B > Π_t; reason: the lemma is algebra in B; the optimum is one such B
--   - reading: D_3(n)r^3/B = O_k(n^{ℓ−3}u^{−(ℓ−3)/ℓ}) → ∃ C (depending on k and c) bounding the ratio for all admissible t, n, r, B with ℓ ≥ 4; reason: O_k with the constant c_k fixed by k
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), Lemma 5.4, p.26

import Mathlib
import Definitions.Def_AcceptSubcube_GInst
import Definitions.Def_AcceptSubcube_cost

namespace AcceptSubcube

/-- **Lemma 5.4 (The additive term).**

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), Lemma 5.4, p.26: "Let 1 ≤ r ≤ n satisfy
r^ℓ ≤ c_k B/Π_t with B > Π_t, and put u = B/Π_t. Then for j ≤ ℓ,
D_j(n) r^j / B ≤ c_k^{j/ℓ} (D_j(n)/Π_t) u^{−(ℓ−j)/ℓ}. In particular, D_ℓ(n) r^ℓ ≤ c_k B, and for
ℓ ≥ 4, D_3(n) r^3/B = O_k(n^{ℓ−3} u^{−(ℓ−3)/ℓ})."

Setting of §5 (p.25): `k ≥ 2`, `0 ≤ t ≤ k − 2`, `ℓ = k − t`, `n ≥ k`, `Π_t = (n choose t)`,
`D_j(n) = (n − j choose k − j)`. Three clauses: (1) the bound for every `j ≤ ℓ`; (2)
`D_ℓ(n) r^ℓ ≤ c_k B`; (3) for `ℓ ≥ 4` a constant `C` (depending on `k` and `c_k` only) with
`D_3(n) r^3/B ≤ C n^{ℓ−3} u^{−(ℓ−3)/ℓ}`.

**Formalization Note.** The lemma is algebra: it is stated for every constant `c_k > 0` (the
paper's `c_k` is that of Lemma 5.3) and every real `B > Π_t` (in the paper `B` is an optimum).
Real powers `c^{j/ℓ}`, `u^{−(ℓ−j)/ℓ}` are `Real.rpow` of positive bases. -/
theorem lemma_5_4 (k : ℕ) (hk : 2 ≤ k) (c : ℝ) (hc : 0 < c) :
    (∀ t : ℕ, t ≤ k - 2 → ∀ n : ℕ, k ≤ n → ∀ r : ℕ, 1 ≤ r → r ≤ n → ∀ B : ℝ,
        (n.choose t : ℝ) < B → (r : ℝ) ^ (k - t) ≤ c * B / (n.choose t : ℝ) →
        (∀ j : ℕ, j ≤ k - t →
          (Dj k j n : ℝ) * (r : ℝ) ^ j / B ≤
            c ^ ((j : ℝ) / ((k - t : ℕ) : ℝ)) * ((Dj k j n : ℝ) / (n.choose t : ℝ)) *
              (B / (n.choose t : ℝ)) ^ (-(((k - t - j : ℕ) : ℝ) / ((k - t : ℕ) : ℝ)))) ∧
        (Dj k (k - t) n : ℝ) * (r : ℝ) ^ (k - t) ≤ c * B) ∧
    (∃ C : ℝ, ∀ t : ℕ, t ≤ k - 2 → 4 ≤ k - t → ∀ n : ℕ, k ≤ n → ∀ r : ℕ, 1 ≤ r → r ≤ n →
        ∀ B : ℝ, (n.choose t : ℝ) < B → (r : ℝ) ^ (k - t) ≤ c * B / (n.choose t : ℝ) →
        (Dj k 3 n : ℝ) * (r : ℝ) ^ 3 / B ≤
          C * (n : ℝ) ^ (k - t - 3) *
            (B / (n.choose t : ℝ)) ^ (-(((k - t - 3 : ℕ) : ℝ) / ((k - t : ℕ) : ℝ)))) := by sorry

end AcceptSubcube
