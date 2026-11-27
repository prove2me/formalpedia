-- Prove2me | Theorems.Thm_AbelianCayleyHDX_explicit_relation_complexes
-- name    : AbelianCayleyHDX.explicit_relation_complexes
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-26T23:23:06.731891+00:00
-- url     : https://prove2.me/theorems/45b40e30-429f-5822-a99a-99e0a0804ecc
-- title:
--   Explicitness of the relation-matrix quotient construction (proof of Theorem 1.2, p.7)
-- statement:
--   Let $j \mapsto H_j \in \mathbb F_2^{R_j \times M_j}$ be a family of *good relation matrices*: the rows of $H_j$ are distinct and have weight three, every column has the same weight $\rho_j > 0$, and the binary row space $\mathrm{rowspan}\,H_j$ has minimum distance at least three. Write $n_j = \dim_{\mathbb F_2} \ker H_j$. Assume:
--
--   1. the family is explicit: one multi-stack Turing machine, given $j$ in binary, outputs $R_j$, $M_j$ and the rows of $H_j$ within $p(M_j)$ steps, for a fixed polynomial $p$;
--   2. the number of columns is polynomial in the dimension: $M_j \le q(n_j)$ for a fixed polynomial $q$.
--
--   Then there are $\mathbb F_2$-linear surjections $\varphi_j : \mathbb F_2^{M_j} \to \mathbb F_2^{n_j}$ with $\ker \varphi_j = \mathrm{rowspan}\,H_j$ such that the family of relation complexes $X_{H_j}$ of Section 2.4 is explicit. Here $X_{H_j}$ is the complex over $\mathbb F_2^{n_j}$ with generators $s_i = \varphi_j(e_i)$ and triangles $\{g,\ g+s_i,\ g+s_i+s_k\}$ for $i \ne k$ in a common row. Explicit means that one algorithm, given $j$, outputs in time polynomial in $n_j$:
--
--   - the dimension $n_j$;
--   - the generators $s_i$;
--   - one representative of each translation orbit of triangles, together with the exact weight $1/|X_{H_j}|$ of each triangle.
--
--   This is the explicitness step of the proof of Theorem 1.2. A basis $B_j$ of $\ker H_j$, found by Gaussian elimination, gives $\varphi_j(v) = B_j v$; the rows of $H_j$ give the orbit representatives. It turns any explicit family of good relation matrices of polynomial size, such as the one of Lemma 2.3, into an explicit family of Cayley complexes.
--
--   **Formalization Note** The maps $\varphi_j$ are existentially quantified; the algorithm determines them. Explicitness is the mission's `IsExplicitFamily` (multi-stack Turing machine `HMBinPacking.OutputsWithin`, binary encodings `encNat`, `encList`, `encVec`, `encRat`).
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.5 (proof of Theorem 1.2), p.7, last paragraph; explicitness as defined in Section 2.3

import Mathlib
import Definitions.Def_AbelianCayleyHDX_IsGoodRelationMatrix
import Definitions.Def_AbelianCayleyHDX_kerF2
import Definitions.Def_AbelianCayleyHDX_relationComplex
import Definitions.Def_AbelianCayleyHDX_IsExplicitFamily
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_ReplParity_Vec
open RSListDecodingCapacity.AllRates
open ReplParity (Vec)

namespace AbelianCayleyHDX

/-- **Explicitness of the quotient construction** (Mao, *Abelian Cayley High-Dimensional Expanders
with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), proof of
Theorem 1.2, Section 2.5, p.7): "Let `B ∈ 𝔽₂^{n×M}` have as its rows a basis of `ker_{𝔽₂} H`. Then
`ker B = rowspan_{𝔽₂} H`, so `v + rowspan H ↦ Bv` identifies `Γ` with `𝔽₂ⁿ`. Under this
identification, the generators are the columns of `B` … Gaussian elimination computes `B`.
Moreover, `R = ρM/3 = n^{O_λ(1)}`, and the rows of `H` give the triangle-orbit representatives …
every triangle has weight `1/(R2ⁿ)`."

Stated as: let `j ↦ H_j` be a family of good relation matrices (distinct weight-three rows,
constant positive column weight `ρ_j`, row space of minimum distance at least three) with `R_j`
rows and `M_j` columns, produced by one multi-stack Turing machine that on input `j` (binary)
outputs `R_j`, `M_j` and the rows of `H_j` within `p(M_j)` steps, and suppose `M_j ≤ q(n_j)` for a
polynomial `q`, where `n_j = dim_{𝔽₂} ker H_j`. Then there are linear surjections
`φ_j : 𝔽₂^{M_j} → 𝔽₂^{n_j}` with kernel `rowspan H_j` such that the family of relation complexes
`X_{H_j}` (generators `φ_j(e_i)`, triangles `{g, g + s_i, g + s_i + s_k}`) is explicit in the
sense of Section 2.3 (`IsExplicitFamily`), with time polynomial in `n_j`.

**Formalization Note** The maps `φ_j` are existentially quantified: the algorithm determines
them (e.g. `φ_j(v) = B_j v` for the basis `B_j` found by Gaussian elimination). The hypothesis
`M_j ≤ q(n_j)` is the paper's `|S_H| = M = n^{O_λ(1)}` (Eq. (2.3)), which makes the running time
polynomial in `n_j`. -/
theorem explicit_relation_complexes (R M ρ : ℕ → ℕ)
    (H : ∀ j, Matrix (Fin (R j)) (Fin (M j)) (ZMod 2)) (hH : ∀ j, IsGoodRelationMatrix (H j) (ρ j))
    (Mach : Turing.TM2ComputableAux Bool Bool) (p : Polynomial ℕ)
    (hMach : ∀ j, HMBinPacking.OutputsWithin Mach (encNat j)
      (encNat (R j) ++ encNat (M j) ++ encList encVec (List.ofFn (H j))) (p.eval (M j)))
    (q : Polynomial ℕ) (hq : ∀ j, M j ≤ q.eval (Module.finrank (ZMod 2) (kerF2 (H j)))) :
    ∃ φ : ∀ j, (Fin (M j) → ZMod 2) →ₗ[ZMod 2] Vec (Module.finrank (ZMod 2) (kerF2 (H j))),
      (∀ j, Function.Surjective (φ j) ∧ LinearMap.ker (φ j) = rowspan (H j)) ∧
      IsExplicitFamily (fun j => Module.finrank (ZMod 2) (kerF2 (H j)))
        (fun j => Finset.univ.image fun i => φ j (Pi.single i 1))
        (fun j => relationComplex (H j) (φ j)) := by sorry

end AbelianCayleyHDX
