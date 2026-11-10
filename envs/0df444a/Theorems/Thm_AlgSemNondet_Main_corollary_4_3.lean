-- Prove2me | Theorems.Thm_AlgSemNondet_Main_corollary_4_3
-- name    : AlgSemNondet.Main.corollary_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:47:50.720089+00:00
-- url     : https://prove2.me/theorems/8391fff7-b99f-4093-a9a6-42939999432c
-- title:
--   Corollary 4.3 — permutation invariance of intrinsic properties
-- statement:
--   Let $\mathfrak P$ be an intrinsic property and $\pi$ a blank-preserving permutation of $\Gamma$. Then for every machine $M$ and every word $w$, $\mathfrak P$ takes the same value on $(M, w)$ and on $(M_\pi, \pi(w))$:
--   $$\mathfrak P(M, w) \iff \mathfrak P(M_\pi, \pi(w)).$$
--
--   Differences from the source:
--   - encoding: a property of a machine on an input → a predicate on machines with fixed state type Q, alphabet Γ and blank B and on all words over Γ; reason: M_π has the same Q, Γ and B, and intrinsicness of a property is unchanged by restricting it to this class
-- source:
--   Zheng, Zheng, Wang and Huang, An Algebraic Semantic Framework for Nondeterministic Computation, July 2026, Corollary 4.3, p.15, held PDF SHA256 729429b16e49937f0b09fd345508cf77ac999be7b0601b781b9e37eb393587fa

import Mathlib
import Definitions.Def_AlgSemNondet_Main_TuringMachine
import Definitions.Def_AlgSemNondet_Main_relabel
import Definitions.Def_AlgSemNondet_Main_IsIntrinsic

namespace AlgSemNondet.Main

/-- Corollary 4.3 (permutation invariance of intrinsic properties): an intrinsic property takes
the same value on `(M, w)` and `(M_π, π(w))` for every blank-preserving permutation `π`. -/
theorem corollary_4_3 {Q Γ : Type*} [Fintype Q] [Fintype Γ] {B : Γ}
    (P : TuringMachine Q Γ B → List Γ → Prop) (hP : IsIntrinsic P)
    (π : Equiv.Perm Γ) (hπB : π B = B) (M : TuringMachine Q Γ B) (w : List Γ) :
    P M w ↔ P (M.relabel π) (w.map π) := by sorry

end AlgSemNondet.Main
