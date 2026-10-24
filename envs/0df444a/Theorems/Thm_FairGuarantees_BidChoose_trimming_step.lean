-- Prove2me | Theorems.Thm_FairGuarantees_BidChoose_trimming_step
-- name    : FairGuarantees.BidChoose.trimming_step
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:45.151+00:00
-- url     : https://prove2.me/theorems/7fce0d08-083a-495a-9853-71372398bca0
-- title:
--   Proposition 1, proof of ii), p. 11 — trimming a better share onto a worse one equalises them
-- statement:
--   Let $\Omega\subseteq\mathbb R^d$ ($d\ge1$) be a manna and $u\in\mathcal D(\Omega)\cap\mathcal M^+(\Omega)$. If $S,T$ are disjoint shares with $u(S)>u(T)$, there is a share $S'\subseteq S$ such that, with $T'=T\cup(S\setminus S')$ (so that $S'$ and $T'$ are disjoint shares),
--   $$
--   u(S')=u(T')\qquad\text{and}\qquad u(T)\le u(S')\le u(S).
--   $$
--
--   This is the basic step of the proof that, for monotone utilities, the benchmarks $\mathit{minMax}$ and $\mathit{Maxmin}$ are the smallest and largest equipartition utilities (Proposition 1 ii)).
--
--   **Formalization Note.** "Disjoint" is exact set disjointness, as on the page.
-- source:
--   Bogomolnaia & Moulin, Guarantees in Fair Division, arXiv:1911.10009v3, p. 11, proof of Proposition 1, Statement ii), first sentence

import Mathlib
import Definitions.Def_FairGuarantees_DivideChoose_Setting
import Definitions.Def_FairGuarantees_BidChoose_Guarantees

open MeasureTheory

namespace FairGuarantees.BidChoose

/-- Proposition 1, proof of ii), p. 11 (the trimming step): for an increasing `u ∈ D(Ω)` and
disjoint shares `S, T` with `u(S) > u(T)`, one can trim a part `S ∖ S'` off `S` and add it to
`T` so that the two resulting disjoint shares `S'` and `T' = T ∪ (S ∖ S')` have equal utility,
lying between `u(T)` and `u(S)`. -/
theorem trimming_step {d : ℕ} (hd : 0 < d) {Ω : Set (FairGuarantees.DivideChoose.E d)} (hΩ : FairGuarantees.DivideChoose.IsManna Ω)
    {u : Set (FairGuarantees.DivideChoose.E d) → ℝ} (hu : FairGuarantees.DivideChoose.IsUtility Ω u) (hinc : FairGuarantees.DivideChoose.IsIncreasing Ω u)
    {S T : Set (FairGuarantees.DivideChoose.E d)} (hS : FairGuarantees.DivideChoose.IsShare Ω S) (hT : FairGuarantees.DivideChoose.IsShare Ω T) (hST : Disjoint S T)
    (hlt : u T < u S) :
    ∃ S' : Set (FairGuarantees.DivideChoose.E d), FairGuarantees.DivideChoose.IsShare Ω S' ∧ S' ⊆ S ∧
      u S' = u (T ∪ (S \ S')) ∧ u T ≤ u S' ∧ u S' ≤ u S := by sorry

end FairGuarantees.BidChoose
