-- Prove2me | Theorems.Thm_AbelianCayleyHDX_triangle_orbits
-- name    : AbelianCayleyHDX.triangle_orbits
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:36:09.165892+00:00
-- url     : https://prove2.me/theorems/2a2bd950-f1e0-4a70-8b72-fa6dcbc5fb40
-- title:
--   Proof of Theorem 1.2 — triangle orbits of $X_H$ have size $2^n$ and correspond to rows
-- statement:
--   Let $H$, $\rho$, $\varphi$ be as in Section 2.4, with $R$ rows. Then:
--   1. every translation orbit of a triangle of $X_H$ has exactly $2^n$ triangles (a nonzero translation of an elementary abelian 2-group cannot stabilize a set of three vertices);
--   2. distinct rows give distinct orbits: if a translate of a triangle $\{g, g+s_i, g+s_i+s_j\}$ of row $r$ equals a triangle $\{g', g'+s_{i'}, g'+s_{i'}+s_{j'}\}$ of row $r'$, then $r = r'$;
--   3. hence $X_H$ has exactly $R \cdot 2^n$ triangles, and under the uniform distribution every triangle has weight $1/(R\,2^n)$.
--
--   Differences from the source:
--   - encoding: $\Gamma_H = \mathbb F_2^M/R_H$ identified with $\mathbb F_2^n$ by $v + R_H \mapsto Bv$ → any $\mathbb F_2$-linear surjection $\varphi : \mathbb F_2^M \to \mathbb F_2^n$ with kernel $R_H$, $s_i = \varphi(e_i)$; reason: every such identification is of this form; the paper's $B$ gives one
--   - encoding: rows $[R]$ and columns $[M]$ → arbitrary finite index types, $M$ = number of columns; reason: a finite type is in bijection with $[M]$; no instance changes
--   - encoding: every triangle has weight $1/(R2^n)$ → $|X_H| = R \cdot 2^n$; reason: under the uniform distribution each triangle has weight $1/|X_H|$
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), proof of Theorem 1.2, Section 2.5, p.10

import Mathlib
import Definitions.Def_AbelianCayleyHDX_IsGoodRelationMatrix
import Definitions.Def_AbelianCayleyHDX_relationComplex
import Definitions.Def_ReplParity_Vec
open ReplParity (Vec)

namespace AbelianCayleyHDX

/-- **Proof of Theorem 1.2: the triangle orbits of `X_H`** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), proof of Theorem 1.2,
Section 2.5, p.10). For `X_H` as in Section 2.4 (`R` rows, `Γ_H ≅ 𝔽₂ⁿ` via `φ`):
1. every translation orbit of a triangle has size `2ⁿ` ("a nonzero translation in an elementary
   abelian 2-group cannot stabilize a set of three vertices");
2. distinct rows give distinct orbits: if a translate of the triangle `{g, g + s_i, g + s_i + s_j}`
   of row `r` is the triangle `{g', g' + s_{i'}, g' + s_{i'} + s_{j'}}` of row `r'`, then `r = r'`;
3. hence `X_H` has exactly `R · 2ⁿ` triangles, and every triangle has weight `1/(R 2ⁿ)`. -/
theorem triangle_orbits {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] {n : ℕ}
    (H : Matrix ι κ (ZMod 2)) (ρ : ℕ) (hH : IsGoodRelationMatrix H ρ)
    (φ : (κ → ZMod 2) →ₗ[ZMod 2] Vec n) (hφ : Function.Surjective φ)
    (hker : LinearMap.ker φ = rowspan H) :
    (∀ τ ∈ relationComplex H φ,
      ((Finset.univ : Finset (Vec n)).image fun g => τ.image (· + g)).card = 2 ^ n) ∧
    (∀ (r r' : ι) (g g' x : Vec n) (i j i' j' : κ), i ≠ j → H r i ≠ 0 → H r j ≠ 0 →
      i' ≠ j' → H r' i' ≠ 0 → H r' j' ≠ 0 →
      ({g, g + φ (Pi.single i 1), g + φ (Pi.single i 1) + φ (Pi.single j 1)} : Finset (Vec n)).image
          (· + x) =
        ({g', g' + φ (Pi.single i' 1), g' + φ (Pi.single i' 1) + φ (Pi.single j' 1)} :
          Finset (Vec n)) → r = r') ∧
    (relationComplex H φ).card = Fintype.card ι * 2 ^ n := by sorry

end AbelianCayleyHDX
