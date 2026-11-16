-- Prove2me | Theorems.Thm_CatalyticMatching_General_Supplement_unique_rank_increase
-- name    : CatalyticMatching.General.Supplement.unique_rank_increase
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:07:26.522818+00:00
-- url     : https://prove2.me/theorems/1e0587cb-a698-4f5e-ad93-f53dbaee4d5b
-- title:
--   Lemma 4.2 (2A′) — a rank-raising one-variable change raises rank at every other value
-- statement:
--   Let $A$ be an $r\times c$ mixed matrix over a field $F$, let $A'$ be an evaluation in which the variable $x_i$ has value $a_i$, and let $b\in F$ satisfy $\operatorname{rank}A'_{x_i\leftarrow b}=\operatorname{rank}A'+1$. Then
--
--   $$\forall\,\tilde a\in F\setminus\{a_i\}:\qquad \operatorname{rank}A'_{x_i\leftarrow\tilde a}=\operatorname{rank}A'+1.$$
--
--   So $a_i$ is the unique value of $x_i$ at which the rank does not increase; this is what lets the catalytic algorithm forget $a_i$ and recover it later.
--
--   Differences from the source:
--   - generalization: §4 fixes F = ℚ (p.22) → any field F; reason: the proof uses only that a determinant is affine in a single entry, valid over every field; F = ℚ is a special case
--   - generalization: a ∈ [n^10] → any b ∈ F; reason: the proof never uses the range of a; a ∈ [n^10] is a special case
--   - encoding: an r×c mixed matrix with rows L_r, columns L_c and variable set X indexed by E → Fin r → Fin c → Option F (none = indeterminate), variables = positions holding none, row/column tags Fin r ⊕ Fin c, A′_{x_i←b} = Function.update of the assignment; reason: relabeling covers every finite rectangular instance, including r = 0 or c = 0; tags keep row u and column u distinct as in L_r ∪ L_c
-- source:
--   Srijan Chakraborty, Samir Datta, Aryan Kusre, Partha Mukhopadhyay, Amit Sinhababu, Maximum Matching and Related Problems in Catalytic Logspace, STOC 2027 submission #479 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/479.pdf, Lemma 4.2, printed/PDF p.23

import Definitions.Def_CatalyticMatching_General_Supplement_MixedMatrix

namespace CatalyticMatching.General.Supplement

/-- Lemma 4.2 (2A′) p.23. Every replacement other than the current value a i raises the
rank by exactly one. Stated over any field and for any witnessing value b. -/
theorem unique_rank_increase {F : Type} [Field F] {r c : ℕ} (A : MixedMatrix r c F)
    (a : MixedVar A → F) (i : MixedVar A) (b : F)
    (hb : (mixedEval A (perturbVar a i b)).rank = (mixedEval A a).rank + 1) :
    ∀ b' : F, b' ≠ a i →
      (mixedEval A (perturbVar a i b')).rank = (mixedEval A a).rank + 1 := by sorry

end CatalyticMatching.General.Supplement
