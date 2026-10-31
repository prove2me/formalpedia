-- Prove2me | Theorems.Thm_CombOpt_ChvatalRank_cut_rotation
-- name    : CombOpt.ChvatalRank.cut_rotation
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:08:32.423056+00:00
-- url     : https://prove2.me/theorems/786593ad-06e4-478f-9bb5-1b6048c38d06
-- title:
--   Lemma 6.33 — a cut for a face rotates to a cut for the polytope
-- statement:
--   Let $F$ be a face of a rational polytope $P$. If $c^Tx\le\lfloor d\rfloor$ is a Gomory–Chvátal cutting plane for $F$, then there exists a Gomory–Chvátal cutting plane $(c')^Tx\le\lfloor d'\rfloor$ for $P$ such that
--   $$
--   F\cap\{x : (c')^Tx\le\lfloor d'\rfloor\}=F\cap\{x : c^Tx\le\lfloor d\rfloor\}.
--   $$
--   This translates a cut that is valid only on a face to a cut for the whole polytope with the same effect on the face.
--
--   **Formalization Note** Cuts are recorded as pairs $(c,t)$ with $t=\lfloor d\rfloor$. The face may be $\emptyset$ or $P$.
--
--   Differences from the source: none.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Lemma 6.33, p. 231 (PDF 239)

import Mathlib
import Definitions.Def_CombOpt_ChvatalRank_IsFace
import Definitions.Def_CombOpt_ChvatalRank_IsGomoryChvatalCut
import Definitions.Def_CombOpt_ChvatalRank_IsRationalPolytope

open Matrix

namespace CombOpt.ChvatalRank

/-- **Lemma 6.33.** Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Lemma 6.33, p. 231 (PDF 239): "Let F be a face of a rational polytope P. If
cᵀx ≤ ⌊d⌋ is a Gomory-Chvátal cutting-plane for F, then there exists a Gomory-Chvátal cutting-plane
(c′)ᵀx ≤ ⌊d′⌋ for P such that F ∩ {x : (c′)ᵀx ≤ ⌊d′⌋} = F ∩ {x : cᵀx ≤ ⌊d⌋}."

**Formalization Note.** `t = ⌊d⌋` and `t′ = ⌊d′⌋` as in `IsGomoryChvatalCut`. `F` may be `∅` or `P`. -/
theorem cut_rotation {n : ℕ} {F P : Set (Fin n → ℝ)} (hP : IsRationalPolytope P) (hF : IsFace F P)
    {c : Fin n → ℝ} {t : ℝ} (hcut : IsGomoryChvatalCut F c t) :
    ∃ (c' : Fin n → ℝ) (t' : ℝ), IsGomoryChvatalCut P c' t' ∧
      F ∩ {x | c' ⬝ᵥ x ≤ t'} = F ∩ {x | c ⬝ᵥ x ≤ t} := by sorry

end CombOpt.ChvatalRank
