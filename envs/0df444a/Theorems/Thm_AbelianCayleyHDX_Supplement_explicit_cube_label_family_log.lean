-- Prove2me | Theorems.Thm_AbelianCayleyHDX_Supplement_explicit_cube_label_family_log
-- name    : AbelianCayleyHDX.Supplement.explicit_cube_label_family_log
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T01:02:03.358235+00:00
-- url     : https://prove2.me/theorems/cc467847-feb2-4450-9494-0014f5b64ef4
-- title:
--   The cube–label Cayley complexes are explicit (index $k_j=|\mathrm{encNat}\,j|$)
-- statement:
--   Fix $d\ge2$ and put $a=d+2$. For $j\ge0$ let $k_j=|\mathrm{encNat}(j)|$ be the length of the binary encoding of $j$, so $k_j\approx2\log_2 j$, and put $n_j=k_j+a$. Consider the cube–label complex over $\mathbb F_2^{n_j}$:
--
--   - its generators are the vectors with nonzero label and cube part in $\{0,e_1,\dots,e_{k_j}\}$;
--   - its top faces are the $(d+1)$-cliques of the Cayley graph;
--   - its top-face distribution $\mu$ gives single-fibre faces weight proportional to $(d-1)k_j$, and faces split $i\,/\,(d+1-i)$ across a cube edge weight proportional to $\binom{d-1}{i-1}^{-1}$.
--
--   This family is **explicit** in the sense of Section 2.3. One multi-stack Turing machine, given $j$ in binary, outputs within time polynomial in $n_j$:
--
--   1. the dimension $n_j$;
--   2. the generators;
--   3. exactly one representative of each translation orbit of top faces, together with its exact rational weight under $\mu$.
--
--   Combined with the proof of the other properties, this gives an explicit family as required in Theorem 1.3, with Cayley degree $(k_j+1)(2^a-1)=\Theta_d(n_j)$ and $n_j\to\infty$.
--
--   **Formalization Note** Explicitness is the mission's `IsExplicitWeightedFamily`. Indexing by $k_j=|\mathrm{encNat}(j)|$ rather than $k_j=j+1$ (as in `explicit_cube_label_family`) makes the output size polynomial in the input length.
-- source:
--   Explicitness notion: Mao, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.3, p.9; family: definition AbelianCayleyHDX_Supplement_cubeLabelComplex, used for Theorem 1.3, p.4

import Mathlib
import Definitions.Def_ReplParity_Vec
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_AbelianCayleyHDX_Supplement_cubeLabelComplex
import Definitions.Def_AbelianCayleyHDX_Supplement_IsExplicitWeightedFamily
open ReplParity (Vec)
open RSListDecodingCapacity.AllRates

namespace AbelianCayleyHDX.Supplement

/-- **The cube–label complexes are explicit, along the index `kⱼ = |encNat j|`** (explicitness in
the sense of Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*,
arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.3, p.9, as required by
Theorem 1.3, p.4). Fix `d ≥ 2` and `a = d + 2`. For each `j` let `k = |encNat j|` (the length of
the binary encoding of `j`, so `k ≈ 2 log₂ j`) and `n = k + a`. One multi-stack Turing machine,
given `j` in binary, outputs `n`, the generators `CubeLabel.gens k a`, one representative of each
translation orbit of the top faces `CubeLabel.tops d k a`, and the exact rational weight
`CubeLabel.mu d k a` of each representative, within time polynomial in `n`.

**Formalization Note** Indexing by `k = |encNat j|` (rather than `k = j + 1`) makes the output
size polynomial in the input length; `n → ∞` along the family. -/
theorem explicit_cube_label_family_log (d : ℕ) (hd : 2 ≤ d) :
    IsExplicitWeightedFamily (fun j => (encNat j).length + (d + 2))
      (fun j => CubeLabel.gens (encNat j).length (d + 2))
      (fun j => CubeLabel.tops d (encNat j).length (d + 2))
      (fun j => CubeLabel.mu d (encNat j).length (d + 2)) := by sorry

end AbelianCayleyHDX.Supplement
