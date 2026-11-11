-- Prove2me | Theorems.Thm_AlgoPrinciplesMulticlass_NoEnvelope_condition1_ds_ge
-- name    : AlgoPrinciplesMulticlass.NoEnvelope.condition1_ds_ge
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:29:05.453305+00:00
-- url     : https://prove2.me/theorems/78496df4-f5ee-483d-ae7e-d977682f22ac
-- title:
--   §3.1, Condition 1 paragraph — a full binary cube on a block gives DS dimension at least d
-- statement:
--   Recall that a non-empty finite set $B\subseteq Y^E$ with $|E|=d$ is a **pseudocube** if for every $f\in B$ and every $x\in E$ there is $g\in B$ with $g(x)\ne f(x)$ and $g(x')=f(x')$ for all $x'\in E\setminus\{x\}$; a set $E\subseteq X$ is **DS-shattered** by a class $F$ if $F{\restriction}E$ contains an $|E|$-dimensional pseudocube; and the **DS dimension** $\mathrm{DS}(F)$ is the supremum of the sizes of the finite DS-shattered sets.
--
--   In the §3.1 construction, let $d\ge1$ and $F\subseteq Y^X$, and suppose Condition 1 holds: some node $v\in T_d$ has, for every $c\in\{0,1\}^d$, a hypothesis $f_c\in F$ with $f_c(x_{d,v,j})=c(j)$ for all $j\in[d]$. Then the restrictions $\{f_c{\restriction}E_{d,v}\}$ contain the full binary cube on $E_{d,v}$, hence a $d$-dimensional pseudocube, and
--   $$\mathrm{DS}(F)\ge d .$$
--
--   In the paper $F=\operatorname{im}(A)$; since $d$ is arbitrary this is one half of $\mathrm{DS}(\operatorname{im}(A))=\infty$.
--
--   **Formalization Note.** $\mathrm{DS}$ is `MulticlassDS.Compress.dsDim` from the published definition `MulticlassDS_Compress_Dimensions`: an `ℕ∞`-valued supremum over DS-shattered *sequences* `Fin n → X`. A sequence with a repeated point is never DS-shattered (a neighbour would have to change one of two equal coordinates), so this is the supremum over finite sets. The bound is `(d : ℕ∞) ≤ dsDim F`.
--
--   Differences from the source:
--   - generalization: im(A) for a PAC learner A of H → an arbitrary class F ⊆ Y^X; reason: the argument uses only Condition 1 for F; taking F = im(A) gives the source's statement
--   - encoding: DS(im(A)) ≥ d, sup over finite DS-shattered sets → `(d : ℕ∞) ≤ MulticlassDS.Compress.dsDim F`, sup over DS-shattered sequences; reason: sequences with a repeated point are never DS-shattered, so the two suprema agree
-- source:
--   Asilis, Dughmi, Sharan, Sun, Teng, Wang, Algorithmic Principles For Multiclass Learning Are Hard To Come By, STOC 2027 submission (manuscript sha256 03e91e8f…), p. 18, §3.1, Condition 1 paragraph

import Mathlib
import Definitions.Def_MulticlassDS_Compress_Dimensions
import Definitions.Def_AlgoPrinciplesMulticlass_NoEnvelope_Construction

namespace AlgoPrinciplesMulticlass.NoEnvelope

/-- §3.1, Condition 1 paragraph (p. 18), for an arbitrary class `F` in place of `im(A)`: if some
block `E_{d,v}` carries the full binary cube `{0,1}^d` in `F↾E_{d,v}`, then `DS(F) ≥ d`. -/
theorem condition1_ds_ge (F : Set (Pt → Label)) (d : ℕ) (hd : 1 ≤ d)
    (h1 : Condition1 F d) :
    (d : ℕ∞) ≤ MulticlassDS.Compress.dsDim F := by sorry

end AlgoPrinciplesMulticlass.NoEnvelope
