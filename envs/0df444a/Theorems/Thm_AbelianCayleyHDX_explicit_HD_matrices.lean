-- Prove2me | Theorems.Thm_AbelianCayleyHDX_explicit_HD_matrices
-- name    : AbelianCayleyHDX.explicit_HD_matrices
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-26T23:38:15.40241+00:00
-- url     : https://prove2.me/theorems/f07c00bf-f733-41df-8e8a-93164beddb89
-- title:
--   Explicitness of the relation matrices $H_D$ (proof of Lemma 2.3, p.14)
-- statement:
--   Let $q=2^h$ and let $F$ be a field with $q^2$ elements, encoded in binary through a fixed bijection $F\to\{0,\dots,q^2-1\}$. Let $j\mapsto D_j\subseteq\mathrm{PG}(t_j-1,F)$ be an explicit family of direction sets: one multi-stack Turing machine, given $j$ in binary, outputs $t_j$ and one nonzero representative of each point of $D_j$ within $p(t_j)$ steps, for a fixed polynomial $p$.
--
--   Then the relation matrices $H_{D_j}$ of Section 3.2 are explicit. Recall that $H_{D_j}$ has columns indexed by $\Omega=F^\times\times F^{t_j}$, so that $M_j=|\Omega|=(q^2-1)q^{2t_j}$, and one row for each triple $(b,x,\ell)$ with $b\in\hat D_j$, $x\in F^{t_j}$ and $\ell\in L_F$; the row $(b,x,\ell)$ has support $\{(p,\,x+pb):p\in\ell\}$. The claim is that there are enumerations of the columns, $\Omega\cong\{0,\dots,M_j-1\}$, and of the rows, $\cong\{0,\dots,R_j-1\}$, and one machine that, given $j$, outputs $R_j$, $M_j$ and the rows of $H_{D_j}$ (in these enumerations) within $p'(M_j)$ steps, for a fixed polynomial $p'$.
--
--   This is the explicitness step of the proof of Lemma 2.3. Since $F$ is fixed, the scalar representatives of $D_j$ and all rows of $H_{D_j}$ can be enumerated by finite-field arithmetic in time polynomial in the output size.
--
--   **Formalization Note** The enumerations are existentially quantified; the algorithm determines them. Explicitness uses the published `HMBinPacking.OutputsWithin` and the encodings `encNat`, `encList`, `encVec`, and `encFVec`.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 3.3 (proof of Lemma 2.3), p.14, last sentence; construction of H_D in Section 3.2

import Mathlib
import Definitions.Def_AbelianCayleyHDX_HD
import Definitions.Def_AbelianCayleyHDX_encFVec
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
open RSListDecodingCapacity.AllRates

namespace AbelianCayleyHDX

/-- **The relation matrices `H_D` are explicit when the direction sets are** (Mao, *Abelian Cayley
High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256
6f5b0daa…75ba), proof of Lemma 2.3, Section 3.3, p.14): "The set `D` is explicit, and, since `F` is
fixed, all scalar representatives and rows of `H` can be enumerated by finite-field arithmetic in
time polynomial in the output size."

Stated as: let `F` be a field with `q² = (2^h)²` elements, fix a bijection `enc : F ≃ {0,…,q²−1}`,
and let `j ↦ D_j ⊆ PG(t_j − 1, F)` be a family of direction sets such that one multi-stack Turing
machine, given `j` in binary, outputs `t_j` and one representative of each point of `D_j` (as
vectors of `F^{t_j}` encoded through `enc`) within `p(t_j)` steps. Then there are enumerations
`e_Ω : Ω = F^× × F^{t_j} ≃ {0,…,M_j−1}` of the columns, `M_j = (q² − 1)q^{2t_j}`, and
`e_R : RowIdx(D_j) ≃ {0,…,R_j−1}` of the rows (triples `(b, x, ℓ)`), and one machine that, given `j`,
outputs `R_j`, `M_j` and the rows of `H_{D_j}` (reindexed by these enumerations) within `p'(M_j)`
steps, for a polynomial `p'`.

**Formalization Note** The enumerations are existentially quantified; the algorithm determines
them. `F` is fixed (finite), so its arithmetic is a finite table. -/
theorem explicit_HD_matrices (h : ℕ) (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = (2 ^ h) ^ 2) (t : ℕ → ℕ) (D : ∀ j, Finset (PG (t j) F))
    (enc : F ≃ Fin (Fintype.card F)) (Mach : Turing.TM2ComputableAux Bool Bool)
    (p : Polynomial ℕ)
    (hMach : ∀ j, ∃ reps : List (Fin (t j) → F), reps.length = (D j).card ∧
      (∀ a ∈ reps, ∃ ha : a ≠ 0, Projectivization.mk F a ha ∈ D j) ∧
      (∀ d ∈ D j, ∃ a ∈ reps, ∃ ha : a ≠ 0, Projectivization.mk F a ha = d) ∧
      HMBinPacking.OutputsWithin Mach (encNat j) (encNat (t j) ++ encList (encFVec enc) reps)
        (p.eval (t j))) :
    ∃ (R : ℕ → ℕ) (eR : ∀ j, RowIdx (D j) ≃ Fin (R j))
      (eΩ : ∀ j, Omega F (t j) ≃ Fin (((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t j)))
      (Mach' : Turing.TM2ComputableAux Bool Bool) (p' : Polynomial ℕ), ∀ j,
      HMBinPacking.OutputsWithin Mach' (encNat j)
        (encNat (R j) ++ encNat (((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t j)) ++
          encList encVec (List.ofFn ((HD (D j)).reindex (eR j) (eΩ j))))
        (p'.eval (((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t j))) := by sorry

end AbelianCayleyHDX
