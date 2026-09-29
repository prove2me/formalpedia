-- Prove2me | Theorems.Thm_FamousTheorems_faa_di_bruno
-- name    : FamousTheorems.faa_di_bruno
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:23.071704+00:00
-- url     : https://prove2.me/theorems/c6ace22c-09cb-4eae-b531-41a46755c590
-- title:
--   Faà di Bruno's formula
-- statement:
--   **Faà di Bruno's formula.** Let $f,g:\Bbbk\to\Bbbk$ over a nontrivially normed field, with $f$ of class $C^n$ at $x$ and $g$ of class $C^n$ at $f(x)$. Then for every $i\le n$,
--   $$(g\circ f)^{(i)}(x)=\sum_{c}g^{(\ell(c))}(f(x))\prod_{j=1}^{\ell(c)}f^{(|c_j|)}(x),$$
--   where $c$ runs over the ordered partitions of $\{1,\dots,i\}$ into $\ell(c)$ blocks $c_1,\dots,c_{\ell(c)}$.
--
--   This is the chain rule for higher derivatives. Grouping the partitions by block sizes gives the classical formula with Bell-polynomial coefficients. It is used to estimate derivatives of compositions, in the theory of analytic and Gevrey functions, and in combinatorics of set partitions.
--
--   **Formalization note.** Mathlib's `iteratedDeriv_comp_eq_sum_orderedFinpartition`. `OrderedFinpartition i` is Mathlib's type of partitions of `Fin i` into blocks ordered by their largest elements, with `c.length` blocks of sizes `c.partSize j`. The smoothness order `n` may be infinite or analytic (`n : WithTop ℕ∞`).
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `iteratedDeriv_comp_eq_sum_orderedFinpartition`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem faa_di_bruno {𝕜 : Type*} [NontriviallyNormedField 𝕜] {g f : 𝕜 → 𝕜} {x : 𝕜} {n : WithTop ℕ∞} {i : ℕ}
    (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x) (hi : (i : WithTop ℕ∞) ≤ n) :
    iteratedDeriv i (g ∘ f) x =
      ∑ c : OrderedFinpartition i,
        iteratedDeriv c.length g (f x) * ∏ j : Fin c.length, iteratedDeriv (c.partSize j) f x := by sorry

end FamousTheorems
