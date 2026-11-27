-- Prove2me | Theorems.Thm_AbelianCayleyHDX_Supplement_explicit_cube_label_family
-- name    : AbelianCayleyHDX.Supplement.explicit_cube_label_family
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-27T00:14:59.960926+00:00
-- url     : https://prove2.me/theorems/97086614-0270-53eb-a6eb-f98205742649
-- title:
--   The cube–label Cayley complexes are explicit
-- statement:
--   Fix $d\ge2$ and put $a=d+2$. For $j\ge0$ let $k=j+1$ and $n=k+a$, and consider the cube–label complex over $\mathbb F_2^{n}$. Its generators are the vectors with nonzero label and cube part in $\{0,e_1,\dots,e_k\}$. Its top faces are the $(d+1)$-cliques of the Cayley graph. Its top-face distribution $\mu$ has weight $(d-1)k$ on single-fibre faces and $\binom{d-1}{j-1}^{-1}$ on faces meeting the two fibres of a cube edge in $j$ and $d+1-j$ points, normalized to total mass $1$.
--
--   The family is **explicit** in the sense of Section 2.3 of the paper. One multi-stack Turing machine, given $j$ in binary, outputs within time polynomial in $n$:
--
--   1. the dimension $n$;
--   2. the generators;
--   3. one representative of each translation orbit of top faces, together with its exact rational weight $\mu$.
--
--   Together with the proof of the remaining properties, this gives an explicit family of weighted $d$-dimensional Cayley complexes as in Theorem 1.3, with Cayley degree $(k+1)(2^a-1)=\Theta_d(n)$.
--
--   **Formalization Note** Explicitness is the mission's `IsExplicitWeightedFamily`: it uses the multi-stack Turing machine run `HMBinPacking.OutputsWithin`, the binary encodings `encNat`, `encList`, `encVec` and `encRat`, and the requirement of exactly one listed representative per translation orbit. The number of orbits is $O_d(k)$, and the weights are explicit rationals of polynomial size.
-- source:
--   Explicitness notion: Mao, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.3, p.9; family: the cube–label construction (definition AbelianCayleyHDX_Supplement_cubeLabelComplex) used for Theorem 1.3, p.4 (variant of Section 5, pp.19–21)

import Mathlib
import Definitions.Def_ReplParity_Vec
import Definitions.Def_AbelianCayleyHDX_Supplement_cubeLabelComplex
import Definitions.Def_AbelianCayleyHDX_Supplement_IsExplicitWeightedFamily
open ReplParity (Vec)

namespace AbelianCayleyHDX.Supplement

/-- **The cube–label complexes are explicit** (in the sense of Mao, *Abelian Cayley
High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256
6f5b0daa…75ba), Section 2.3, p.9, as used for Theorem 1.3, p.4). For fixed `d ≥ 2`, `a = d + 2`
and `k = j + 1`, one multi-stack Turing machine, given `j` in binary, outputs `n = k + a`, the
generators of `CubeLabel.gens k a`, one representative of each translation orbit of
`CubeLabel.tops d k a` and its exact rational weight `CubeLabel.mu d k a`, within time polynomial
in `n`.

**Formalization Note** The number of orbits is `O_d(k)` and the weights are explicit rationals
(the total weight is a polynomial in `k` for fixed `d`), so the output has polynomial size. -/
theorem explicit_cube_label_family (d : ℕ) (hd : 2 ≤ d) :
    IsExplicitWeightedFamily (fun j => (j + 1) + (d + 2)) (fun j => CubeLabel.gens (j + 1) (d + 2))
      (fun j => CubeLabel.tops d (j + 1) (d + 2)) (fun j => CubeLabel.mu d (j + 1) (d + 2)) := by
  sorry

end AbelianCayleyHDX.Supplement
