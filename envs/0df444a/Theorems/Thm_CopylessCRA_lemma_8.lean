-- Prove2me | Theorems.Thm_CopylessCRA_lemma_8
-- name    : CopylessCRA.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:47:26.668195+00:00
-- url     : https://prove2.me/theorems/ac7db533-78ca-4ba1-9042-7e4d0eac90be
-- title:
--   Lemma 8, p.8 — $P$ maps onto $L_P$, $\operatorname{rank}B_P=2^{k(P)}$, $\ker B_P$ = polynomials vanishing on $L_P$
-- statement:
--   Let $P:\mathbb Q^r\to\mathbb Q^r$ be a copyless map, $k(P)$ the number of its nonconstant coordinates and $L_P$ the coordinate affine subspace obtained by fixing each constant coordinate to its value. Then
--
--   1. $P$ maps $\mathbb Q^r$ onto $L_P(\mathbb Q)$;
--   2. $\operatorname{rank}B_P=\dim B_P(V_r)=2^{k(P)}$;
--   3. $\ker B_P=\{h\in V_r:h|_{L_P}=0\}$, i.e. for $h\in V_r$, $h\circ P=0$ iff $h$ vanishes at every rational point of $L_P$.
--
--   Differences from the source:
--   - generalization: copyless maps given by syntactic copyless tuples (§2.1) → maps with multiaffine coordinates and pairwise disjoint variable supports (`IsCopylessMap`); reason: every syntactic copyless tuple is such a map (proved in `Solutions/verification/CopylessCRA_syntactic.lean`), so the statement specializes to the paper's
-- source:
--   Zeng–Cao–Dai–Wang–Ding, Copyless Cost Register Automata and Algebraic Groups, STOC 2027 submission (manuscript sha256 434d3094df2665371c402d5b5291b3c7f3a27a0d79384e4a8ec3ca3a46a92543), Lemma 8, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_CopylessCRA_CCRA
import Definitions.Def_CopylessCRA_IsCopylessMap

namespace CopylessCRA

/-- **Lemma 8.** `P` maps `ℚ^r` onto `L_P(ℚ)`, `rank B_P = 2^{k(P)}`, and
`ker B_P = {h ∈ V_r : h|_{L_P} = 0}`.

Zeng–Cao–Dai–Wang–Ding, *Copyless Cost Register Automata and Algebraic Groups*, STOC 2027
submission (manuscript sha256 434d3094…), Lemma 8, p.8 (PDF p.10).

**Formalization Note** `P : ℚ^r → ℚ^r` is a copyless map (semantic sense: multiaffine coordinates
with disjoint supports). `B_P` acts on `V_r`; its rank is the dimension of `B_P(V_r)`, and
`h|_{L_P} = 0` means that `h` vanishes at every rational point of `L_P`. -/
theorem lemma_8 {r : ℕ} (P : Fin r → MvPolynomial (Fin r) ℚ) (hP : IsCopylessMap P) :
    Set.range (evalMap P) = coordSubspace P ∧
    Module.finrank ℚ ((multiaffine r).map (pullback P)) = 2 ^ numFree P ∧
    ∀ h ∈ multiaffine r,
      (pullback P h = 0 ↔ ∀ x ∈ coordSubspace P, MvPolynomial.eval x h = 0) := by sorry

end CopylessCRA
