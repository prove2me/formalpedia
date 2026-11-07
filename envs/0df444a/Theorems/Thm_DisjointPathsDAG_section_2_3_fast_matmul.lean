-- Prove2me | Theorems.Thm_DisjointPathsDAG_section_2_3_fast_matmul
-- name    : DisjointPathsDAG.section_2_3_fast_matmul
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:31:43.739169+00:00
-- url     : https://prove2.me/theorems/60161170-9c1b-481a-ad0b-7719a0b406ea
-- title:
--   Section 2.3 — $h\times h$ products over $\mathbb F_{2^q}$ in $O(h^{\omega+\varepsilon})$ by linear-time constructible programs
-- statement:
--   Let $\omega$ be the exponent of square matrix multiplication by bilinear algorithms with coefficients in $\mathbb F_2$. For every $\varepsilon>0$ there are a constant $C$ and a generator program such that:
--
--   1. for every $h\ge1$, the generator writes, within $C(\text{size}+1)$ machine steps, a division-free program with constants $0,1$ of size at most $C\,h^{\omega+\varepsilon}$ that computes the product of two $h\times h$ matrices as an identity of formal polynomials over every commutative ring of characteristic $2$, in particular over every $\mathbb F_{2^q}$;
--   2. for every $h\ge1$ and $p$, an $h\times p$ by $p\times h$ product has such a program of size at most $\lceil p/h\rceil\,(C\,h^{\omega+\varepsilon}+h^2)$, and for $h\le p$ an $h\times h$ by $h\times p$ product has one of size at most $\lceil p/h\rceil\,C\,h^{\omega+\varepsilon}$.
--
--   This supplies the matrix-multiplication hypothesis of Theorem 4.1 and Proposition 4.6 with $\alpha=\omega+\varepsilon$, which is how $\omega$ enters Theorem 4.7.
--
--   Differences from the source:
--   - generalization: over every field $\mathbb F_{2^q}$ → over every commutative ring of characteristic 2; reason: contains every $\mathbb F_{2^q}$; specializes to the source
--   - reading: "An h × p by p × h product, or an h × h by h × p product with h ≤ p" → $h\le p$ required for the second shape only; reason: the stronger of the two readings; the first shape pads to one square block when $p<h$
--   - encoding: "splits into ⌈p/h⌉ square products" → a program of size at most $\lceil p/h\rceil(Ch^{\omega+\varepsilon}+h^2)$, resp. $\lceil p/h\rceil Ch^{\omega+\varepsilon}$; reason: the cost of the split: the square products plus the additions that sum them
--   - encoding: $\omega$ → `MME.matMulExp (ZMod 2)`; reason: the exponent defined by tensor rank over $\mathbb F_2$, i.e. bilinear complexity
--   - encoding: "constructed in time linear in its length" → `GeneratesSLP`: the generator halts within `C * (size + 1)` steps on every tape; reason: the machine of Section 2.1
-- source:
--   Cao–Qi–Wang, Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths, arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Section 2.3, p.7

import Mathlib
import Definitions.Def_DisjointPathsDAG_Machine
import Definitions.Def_mme_omega

set_option autoImplicit false

namespace DisjointPathsDAG

/-- Cao–Qi–Wang, *Faster Algorithms for Disjoint Paths in DAGs and Two Disjoint Shortest Paths*,
arXiv:2611.02154 (held version, sha256 2d2202de…7e17), Section 2.3, p.7: "A bilinear algorithm with
coefficients in F2 is a division-free straight-line program over every field F2q. Hence, for every
fixed ε > 0, applying such an algorithm of exponent below ω + ε recursively multiplies two h × h
matrices over F2q with O(hω+ε) field operations, by a program constructed in time linear in its length.
An h × p by p × h product, or an h × h by h × p product with h ≤ p, splits into ⌈p/h⌉ square products."

Here `ω = MME.matMulExp (ZMod 2)`, the exponent of square matrix multiplication by bilinear algorithms
with coefficients in `F₂` (tensor rank over `F₂`). For every `ε > 0` there are a constant `C` and a
machine program `Gen` such that:
1. for every `h ≥ 1`, `Gen` on input `h` writes, within `C · (size + 1)` steps, a program of size at most
   `C · h^(ω+ε)` with constants `0, 1` that computes the `h × h` matrix product as an identity of formal
   polynomials over every commutative ring of characteristic `2` (in particular over every `F_{2^q}`);
2. for `h ≥ 1` and every `p`, the `h × p` by `p × h` product has a program of size at most
   `⌈p/h⌉ · (C · h^(ω+ε) + h²)` (`⌈p/h⌉` square products and the additions of their sums), and for
   `h ≤ p` the `h × h` by `h × p` product has one of size at most `⌈p/h⌉ · C · h^(ω+ε)`, both formal
   over every commutative ring of characteristic `2`.

**Formalization Note** Matrix entries are inputs and outputs in row-major layout (`ComputesMatMul`).
`natTable` names integer constants, which in characteristic `2` are `0` and `1`. -/
theorem section_2_3_fast_matmul :
    ∀ ε : ℝ, 0 < ε → ∃ (C : ℝ) (A : ℕ) (Gen : Program), 0 < C ∧ 1 ≤ A ∧
      (∀ h : ℕ, 1 ≤ h → GeneratesSLP Gen A [h] C fun P =>
        (∀ (R : Type) [CommRing R] [CharP R 2], ComputesMatMul R (natTable R) h h h P) ∧
        (P.size : ℝ) ≤ C * (h : ℝ) ^ (MME.matMulExp (ZMod 2) + ε)) ∧
      (∀ h p : ℕ, 1 ≤ h →
        (∃ P₁ : SLP, (∀ (R : Type) [CommRing R] [CharP R 2], ComputesMatMul R (natTable R) h p h P₁) ∧
          (P₁.size : ℝ) ≤ (⌈(p : ℝ) / h⌉₊ : ℝ) *
            (C * (h : ℝ) ^ (MME.matMulExp (ZMod 2) + ε) + (h : ℝ) ^ 2)) ∧
        (h ≤ p → ∃ P₂ : SLP,
          (∀ (R : Type) [CommRing R] [CharP R 2], ComputesMatMul R (natTable R) h h p P₂) ∧
          (P₂.size : ℝ) ≤ (⌈(p : ℝ) / h⌉₊ : ℝ) * (C * (h : ℝ) ^ (MME.matMulExp (ZMod 2) + ε)))) := by sorry

end DisjointPathsDAG
