-- Prove2me | Theorems.Thm_CatalyticMatching_General_Supplement_replacement_rank_bound
-- name    : CatalyticMatching.General.Supplement.replacement_rank_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:07:57.030694+00:00
-- url     : https://prove2.me/theorems/d5ca86ff-950b-4c26-a39b-f1ffd3273c83
-- title:
--   Claim 4.4 — in the setting of Lemma 4.3, no other replacement exceeds rank k
-- statement:
--   Let $A$ be an $r\times c$ mixed matrix over a field $F$, $A'$ an evaluation with $x_i=a_i$ and $\operatorname{rank}A'=k$, and $b\in F$ with $\operatorname{rank}A'_{x_i\leftarrow b}=k$. Suppose some row or column tag $u$ lies in $D(A'_{x_i\leftarrow b})\setminus D(A')$. Then
--
--   $$\forall\,\tilde a\in F\setminus\{a_i\}:\qquad \operatorname{rank}A'_{x_i\leftarrow\tilde a}\le k.$$
--
--   This bound is the step of Lemma 4.3 showing that the persisting nonsingular minor has maximum size.
--
--   Differences from the source:
--   - reading: Claim 4.4 appears inside the proof of Lemma 4.3 and inherits its setting → every hypothesis of Lemma 4.3 (ranks k at A′ and at A′_{x_i←b}, a chosen u ∈ D(A′_{x_i←b}) \ D(A′)) is an explicit hypothesis; reason: the claim is stated and proved in that context on p.23
--   - generalization: §4 fixes F = ℚ (p.22) → any field F; reason: the proof uses only that a determinant is affine in a single entry, valid over every field; F = ℚ is a special case
--   - generalization: a ∈ [n^10] → any b ∈ F; reason: the proof never uses the range of a; a ∈ [n^10] is a special case
--   - encoding: an r×c mixed matrix with rows L_r, columns L_c and variable set X indexed by E → Fin r → Fin c → Option F (none = indeterminate), variables = positions holding none, row/column tags Fin r ⊕ Fin c, A′_{x_i←b} = Function.update of the assignment; reason: relabeling covers every finite rectangular instance, including r = 0 or c = 0; tags keep row u and column u distinct as in L_r ∪ L_c
-- source:
--   Srijan Chakraborty, Samir Datta, Aryan Kusre, Partha Mukhopadhyay, Amit Sinhababu, Maximum Matching and Related Problems in Catalytic Logspace, STOC 2027 submission #479 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/479.pdf, Claim 4.4 (inside the proof of Lemma 4.3), printed/PDF p.23

import Definitions.Def_CatalyticMatching_General_Supplement_MixedMatrix

namespace CatalyticMatching.General.Supplement

/-- Claim 4.4 p.23, in the complete setting of Lemma 4.3: equal ranks k at a and at b,
and a chosen newly deficient tagged row or column u. -/
theorem replacement_rank_bound {F : Type} [Field F] {r c : ℕ} (A : MixedMatrix r c F)
    (a : MixedVar A → F) (i : MixedVar A) (b : F) (k : ℕ)
    (hbase : (mixedEval A a).rank = k)
    (hequal : (mixedEval A (perturbVar a i b)).rank = k)
    (u : Tag r c)
    (hu : u ∈ rectDeficiency (mixedEval A (perturbVar a i b)) \ rectDeficiency (mixedEval A a)) :
    ∀ b' : F, b' ≠ a i → (mixedEval A (perturbVar a i b')).rank ≤ k := by sorry

end CatalyticMatching.General.Supplement
