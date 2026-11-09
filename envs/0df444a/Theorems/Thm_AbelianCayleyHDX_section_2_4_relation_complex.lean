-- Prove2me | Theorems.Thm_AbelianCayleyHDX_section_2_4_relation_complex
-- name    : AbelianCayleyHDX.section_2_4_relation_complex
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:35:43.2875+00:00
-- url     : https://prove2.me/theorems/ed4c0bce-7502-479a-8ceb-3844dce4f034
-- title:
--   Section 2.4 — $X_H$ is a translation-invariant Cayley complex with link operator $P_H$ (Eq. (2.1))
-- statement:
--   Let $H$ be a binary relation matrix with distinct rows of weight three, constant positive column weight $\rho$ and row space $R_H$ of minimum distance at least three. Identify $\Gamma_H = \mathbb F_2^M/R_H$ with $\mathbb F_2^n$ by a linear surjection $\varphi$ with kernel $R_H$, and let $s_i = \varphi(e_i)$. Then:
--   1. the $s_i$ are nonzero and pairwise distinct, they span, and $n = \dim_{\mathbb F_2}\ker H$;
--   2. if a row of $H$ has support $\{i,j,k\}$ then $s_i + s_j + s_k = 0$;
--   3. two distinct rows share at most one column of their supports;
--   4. $X_H$ is a translation-invariant unweighted two-dimensional Cayley complex over $\mathbb F_2^n$ with generators $S_H = \{s_i\}$, its Cayley degree is $|S_H| = M$, and every edge lies in $2\rho$ triangles;
--   5. the link of $X_H$ at $0$ has vertex set $S_H$, is $2\rho$-regular, and its adjacency matrix (indexed by columns via $i \mapsto s_i$) is $\tilde H^{\mathsf T}\tilde H - \rho I_M$, so its normalized adjacency operator is
--   $$P_H = \frac{\tilde H^{\mathsf T}\tilde H - \rho I_M}{2\rho}. \qquad (2.1)$$
--
--   This reduces Theorem 1.2 to relation matrices.
--
--   Differences from the source:
--   - encoding: $\Gamma_H = \mathbb F_2^M/R_H$ identified with $\mathbb F_2^n$ by $v + R_H \mapsto Bv$ → any $\mathbb F_2$-linear surjection $\varphi : \mathbb F_2^M \to \mathbb F_2^n$ with kernel $R_H$, $s_i = \varphi(e_i)$; reason: every such identification is of this form; the paper's $B$ gives one
--   - encoding: rows $[R]$ and columns $[M]$ → arbitrary finite index types, $M$ = number of columns; reason: a finite type is in bijection with $[M]$; no instance changes
--   - encoding: simple, pure, unweighted complex → a `Finset` of 3-sets with the uniform distribution; reason: a `Finset` holds each face once; uniform = unweighted
--   - encoding: the link at the identity has adjacency matrix $\tilde H^{\mathsf T}\tilde H - \rho I_M$ → the unnormalized link weights between $s_i$ and $s_j$ equal the $(i,j)$ entries, the link vertex set is $S_H$, and link degrees are $2\rho$; reason: link weights are $1$ on link edges and $0$ otherwise, so they are the adjacency matrix
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.4, p.9, including Eq. (2.1)

import Mathlib
import Definitions.Def_AbelianCayleyHDX_IsGoodRelationMatrix
import Definitions.Def_AbelianCayleyHDX_kerF2
import Definitions.Def_AbelianCayleyHDX_Htilde
import Definitions.Def_AbelianCayleyHDX_relationComplex
import Definitions.Def_AbelianCayleyHDX_IsCayleyComplex
import Definitions.Def_AbelianCayleyHDX_IsTranslationInvariant
import Definitions.Def_AbelianCayleyHDX_linkVerts
import Definitions.Def_AbelianCayleyHDX_linkWeight
import Definitions.Def_ReplParity_Vec
open ReplParity (Vec)

namespace AbelianCayleyHDX

/-- **Section 2.4: the complex `X_H` and Eq. (2.1)** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.4, p.9). Let `H` be a
binary matrix with distinct rows of weight three, constant positive column weight `ρ` and row space
`R_H` of minimum distance at least three, and identify `Γ_H = 𝔽₂^κ / R_H` with `𝔽₂ⁿ` by a linear
surjection `φ` with kernel `R_H`, so `s_i = φ(e_i)`. Then:
1. the `s_i` are nonzero, pairwise distinct and span, and `n = dim_{𝔽₂} ker H`;
2. if a row of `H` has support `{i, j, k}` then `s_i + s_j + s_k = 0`;
3. two distinct row supports share at most one column;
4. `X_H` is a translation-invariant unweighted two-dimensional Cayley complex over `𝔽₂ⁿ` with
   generators `S_H = {s_i}` of Cayley degree `|S_H| = M` (the number of columns), and every edge
   lies in `2ρ` triangles;
5. the link of `X_H` at `0` has vertex set `S_H`, is `2ρ`-regular, and its adjacency matrix,
   indexed by the columns through `i ↦ s_i`, is `H̃ᵀ H̃ − ρ I_M`; hence its normalized adjacency
   operator is `P_H` of (2.1).

**Formalization Note** Simplicity and the uniform distribution are built into the triangle-set
encoding. Clause 5's adjacency entries are the unnormalized link weights (`1` on a link edge). -/
theorem section_2_4_relation_complex {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] {n : ℕ}
    (H : Matrix ι κ (ZMod 2)) (ρ : ℕ) (hH : IsGoodRelationMatrix H ρ)
    (φ : (κ → ZMod 2) →ₗ[ZMod 2] Vec n) (hφ : Function.Surjective φ)
    (hker : LinearMap.ker φ = rowspan H) :
    (∀ i : κ, φ (Pi.single i 1) ≠ 0) ∧
    Function.Injective (fun i : κ => φ (Pi.single i 1)) ∧
    Submodule.span (ZMod 2) (Set.range fun i : κ => φ (Pi.single i 1)) = ⊤ ∧
    n = Module.finrank (ZMod 2) (kerF2 H) ∧
    (∀ r : ι, ∑ i ∈ Finset.univ.filter (fun i => H r i ≠ 0), φ (Pi.single i 1) = 0) ∧
    (∀ r r' : ι, r ≠ r' →
      ((Finset.univ.filter fun i => H r i ≠ 0) ∩ (Finset.univ.filter fun i => H r' i ≠ 0)).card ≤ 1) ∧
    IsCayleyComplex (Finset.univ.image fun i : κ => φ (Pi.single i 1)) (relationComplex H φ) ∧
    IsTranslationInvariant (relationComplex H φ) ∧
    (Finset.univ.image fun i : κ => φ (Pi.single i 1)).card = Fintype.card κ ∧
    (∀ e ∈ edges (relationComplex H φ), triCount (relationComplex H φ) e = 2 * ρ) ∧
    linkVerts (relationComplex H φ) 0 = Finset.univ.image (fun i : κ => φ (Pi.single i 1)) ∧
    (∀ u ∈ linkVerts (relationComplex H φ) 0,
      ∑ w ∈ linkVerts (relationComplex H φ) 0, linkWeight (relationComplex H φ) 0 u w = 2 * (ρ : ℝ)) ∧
    (∀ i j : κ, linkWeight (relationComplex H φ) 0 (φ (Pi.single i 1)) (φ (Pi.single j 1)) =
      ((Htilde H).transpose * Htilde H - (ρ : ℝ) • (1 : Matrix κ κ ℝ)) i j) := by sorry

end AbelianCayleyHDX
