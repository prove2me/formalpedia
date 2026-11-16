-- Prove2me | Theorems.Thm_CatalyticMatching_General_Supplement_persistent_deficiency
-- name    : CatalyticMatching.General.Supplement.persistent_deficiency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:08:28.876568+00:00
-- url     : https://prove2.me/theorems/37ea7f3b-1746-4905-8388-f706e7f60c0c
-- title:
--   Lemma 4.3 (2B′) — a newly deficient row or column persists at every other value
-- statement:
--   Let $A$ be an $r\times c$ mixed matrix over a field $F$, $A'$ an evaluation with $x_i=a_i$ and $\operatorname{rank}A'=k$, and $b\in F$ with $\operatorname{rank}A'_{x_i\leftarrow b}=k$. Let $u$ be any row or column tag with $u\in D(A'_{x_i\leftarrow b})\setminus D(A')$. Then
--
--   $$\forall\,\tilde a\in F\setminus\{a_i\}:\qquad u\in D(A'_{x_i\leftarrow\tilde a}).$$
--
--   So $a_i$ is the unique value of $x_i$ for which $u\notin D$; the algorithm stores $u$ in place of $a_i$ and recovers $a_i$ from this characterization.
--
--   Differences from the source:
--   - reading: "Suppose ∃u ∈ D(A′_{x_i←a}) \ D(A′). Then ∀ã ≠ a_i, u ∈ D(A′_{x_i←ã})" with u used in the conclusion → u is universally bound as any chosen newly deficient row or column tag, before the quantifier over replacements; reason: the proof on p.23 fixes such a u and proves membership for that same u; Algorithm step 2B′ stores that u
--   - generalization: §4 fixes F = ℚ (p.22) → any field F; reason: the proof uses only that a determinant is affine in a single entry, valid over every field; F = ℚ is a special case
--   - generalization: a ∈ [n^10] → any b ∈ F; reason: the proof never uses the range of a; a ∈ [n^10] is a special case
--   - encoding: an r×c mixed matrix with rows L_r, columns L_c and variable set X indexed by E → Fin r → Fin c → Option F (none = indeterminate), variables = positions holding none, row/column tags Fin r ⊕ Fin c, A′_{x_i←b} = Function.update of the assignment; reason: relabeling covers every finite rectangular instance, including r = 0 or c = 0; tags keep row u and column u distinct as in L_r ∪ L_c
-- source:
--   Srijan Chakraborty, Samir Datta, Aryan Kusre, Partha Mukhopadhyay, Amit Sinhababu, Maximum Matching and Related Problems in Catalytic Logspace, STOC 2027 submission #479 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/479.pdf, Lemma 4.3, printed/PDF p.23

import Definitions.Def_CatalyticMatching_General_Supplement_MixedMatrix

namespace CatalyticMatching.General.Supplement

/-- Lemma 4.3 (2B′) p.23. Reading: the printed ∃u fixes any chosen newly deficient tag u,
as in the proof; that same u is deficient after every replacement other than a i. -/
theorem persistent_deficiency {F : Type} [Field F] {r c : ℕ} (A : MixedMatrix r c F)
    (a : MixedVar A → F) (i : MixedVar A) (b : F) (k : ℕ)
    (hbase : (mixedEval A a).rank = k)
    (hequal : (mixedEval A (perturbVar a i b)).rank = k)
    (u : Tag r c)
    (hu : u ∈ rectDeficiency (mixedEval A (perturbVar a i b)) \ rectDeficiency (mixedEval A a)) :
    ∀ b' : F, b' ≠ a i → u ∈ rectDeficiency (mixedEval A (perturbVar a i b')) := by sorry

end CatalyticMatching.General.Supplement
