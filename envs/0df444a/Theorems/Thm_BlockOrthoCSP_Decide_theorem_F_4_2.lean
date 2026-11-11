-- Prove2me | Theorems.Thm_BlockOrthoCSP_Decide_theorem_F_4_2
-- name    : BlockOrthoCSP.Decide.theorem_F_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:15:02.049904+00:00
-- url     : https://prove2.me/theorems/c8c6b664-e05c-49ab-9438-5e6b42245efa
-- title:
--   Theorem F.4.2 — the BO locus $B_k$ is the union of the certificate varieties $V_K(E_c)$, $c \in C_k$ (a finite family)
-- statement:
--   Let $\mathcal F$ be a finite set of algebraic-valued constraint functions on $D$, $q\ge 1$, $K$ its field (F.13). For every arity $k \ge 2$ the family $C_k$ of retained Block Orthogonality certificates is finite and
--   $$B_k = \bigcup_{c \in C_k} V_K(E_c). \qquad (F.24)$$
--   So having a block-orthogonal purification is, at each arity, a finite disjunction of polynomial systems in the original values.
--
--   Differences from the source:
--   - encoding: D = {0, …, q − 1} → Fin q; reason: the same set
--   - encoding: a finite set F of functions f : D^{r_f} → C (C = algebraic complex numbers), r_f ≥ 1 → F : Finset (CFn q) with IsAlgLanguage F (every arity ≥ 1, every value IsAlgebraic ℚ in ℂ); reason: the paper's field C is the algebraic numbers inside ℂ; absolute values and conjugation are those of ℂ
--   - encoding: a function of arity r ≥ 2 (or k ≥ 2), rows F(x, ∗) indexed by x ∈ D^{r−1} → arity j + 1 with 1 ≤ j; rows indexed by Fin j → Fin q, the column is the last coordinate (Fin.snoc); reason: the same functions; writing r = j + 1 avoids natural-number subtraction
--   - reading: 'the effectively enumerable certificate family C_k' → (certs F j).Finite as a conjunct; the effective part is the computability clause of Corollary F.4.4; reason: the adjective states finiteness and enumerability; finiteness is stated here, and the effective construction of Q_k from the certificates is stated in Corollary F.4.4
--   - reading: B_k: the K-valued k-ary functions 'whose singleton purifications are block-orthogonal' → every legal singleton purification is block-orthogonal; reason: the paper notes the property is independent of the purification (Lemma F.3.1)
--   - reading: twisted minors for 'every two distinct rows x, y ∈ R_i and every two distinct columns c, e ∈ C_i' → one root τ and one equation per ordered pair (x, y) and ordered pair (c, e); reason: the union of the varieties is the same under the unordered reading: each ordered-pair certificate contains the equations of an unordered one, and the swapped equations are implied for consistent choices
-- source:
--   Liu, Meng, From Block Orthogonality to Decidability in Complex-Weighted Counting CSP, arXiv:2608.14845 (PDF sha256 ad21e5d7…), p. F-16, Theorem F.4.2

import Mathlib
import Definitions.Def_BlockOrthoCSP_Decide_Instance
import Definitions.Def_BlockOrthoCSP_Decide_Certificate

namespace BlockOrthoCSP.Decide

/-- Theorem F.4.2 (algebraic description of the BO locus), p. F-16, for arity `k = j + 1 ≥ 2`:
the certificate family `C_k` is finite and `B_k = ⋃_{c ∈ C_k} V_K(E_c)`. -/
theorem theorem_F_4_2 {q : ℕ} (hq : 1 ≤ q) (F : Finset (CFn q)) (hF : IsAlgLanguage F)
    (j : ℕ) (hj : 1 ≤ j) :
    (certs F j).Finite ∧ Bk F j = ⋃ d ∈ certs F j, VK F d.eqs := by sorry

end BlockOrthoCSP.Decide
