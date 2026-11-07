-- Prove2me | Theorems.Thm_FewInnerTSP_lemma_5_4
-- name    : FewInnerTSP.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:35:58.040209+00:00
-- url     : https://prove2.me/theorems/d3b45723-cc06-42c5-8e58-84fd0d6043ec
-- title:
--   Lemma 5.4 (Recursive completion domination)
-- statement:
--   Let $P$ be $n\ge3$ points in general position and $\Gamma$ a convex skeleton on them. Let the base threshold satisfy $a_0>17$ and the balance coefficient $\gamma$ satisfy $\gamma\sqrt{a_0}\ge17$, so that the balancing set of every nonbase call has more than $17$ points. Let the separator rule be valid (a minimum balancing square, $t\in[1,3]$, no vertex on the separator's boundary) and the tie rule injective.
--
--   Then for every well-formed state $S$ on $\Gamma$, with **arbitrary** assigned edge weights, the family returned by MixedRepr (Algorithm 2) dominates packing-compliant covers in the sense of Definition 5.1: every member is a feasible cover of $S$, and for every feasible cover $C$ whose free edges are packing-compliant (for the fixed geometry of $P$) and every external matching $X$ with $M(C)\cup X$ connected, some member $R$ has $w(R)\le w(C)$ and $M(R)\cup X$ connected.
--
--   This is the correctness of the recursion: a no-more-expensive completion survives for every compliant witness, even though the representatives themselves need not be compliant.
--
--   **Formalization Note** MixedRepr is run with fuel $|V|+1$, which suffices because every split is balanced.
--
--   Differences from the source:
--   - generalization: MixedRepr with the page's choices: a0 > 17 sufficiently large, γ as in (15), the separator of Lemma 4.5, a fixed tie rule → every a₀ > 17 and γ with γ√a₀ ≥ 17, every valid separator rule and every injective tie rule; reason: the page's choices satisfy these hypotheses, so the statement specializes to them
--   - generalization: the fixed reduced skeleton of §3 → any convex skeleton of any general-position P with n ≥ 3; reason: the proof uses only the state's structure and the packing of the witness; it specializes to the reduced skeleton
--   - reading: Increasing constants if necessary ensures that the chosen balancing set always has more than seventeen points on a nonbase call → the hypotheses a₀ > 17 and γ√a₀ ≥ 17, which imply it; reason: this is what 'increasing constants' secures
--   - encoding: CrossingChoices of Algorithm 1 with a universal long-edge cap and λ per bucket, down to scale 2^{−J} → the filter of subsets of E with ≤ λ long edges and ≤ λ edges in every medium bucket at every scale; reason: App. F gives λ for long edges too; with clearance no straddling edge has a shorter class, so no witness is lost
--   - encoding: the recursion terminates by balance → the Lean function with fuel |V| + 1; reason: a fuel argument avoids proving termination inside the definition; |V| + 1 never runs out
--   - reading: packing-compliant: 'the preceding square packing bounds with the fixed universal constants' (Definition 3.4; two forms and their rescalings, constants unnamed) → IsPackingCompliant: Lemma F.1's one bound with p₀ = 32768, on closed squares; reason: Appendices B.4 and F derive every cap from this single form through constant covers; this class contains the page's, so the clause for every compliant witness is at least as strong
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), Lemma 5.4, p.11 (PDF p.13); Algorithm 2, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_FewInnerTSP_MixedRepr

namespace FewInnerTSP

/-- **Lemma 5.4 (Recursive completion domination).** Li, Ma, Gong, *Exact Euclidean TSP with Few Interior
Points: A Square-Root Exponent*, STOC 2027 submission (manuscript sha256 6541f631…), Lemma 5.4, p.11
(PDF p.13), with Algorithm 2, p.20 (PDF p.22): "MixedRepr returns a family satisfying definition 5.1. The
assertion remains true for arbitrary assigned edge weights, provided the same geometry is used to recognize
packing-compliant witnesses."

Let `P` be `n ≥ 3` points in general position and `Γ` a convex skeleton on them. Let the base threshold
`a₀ > 17` and the balance coefficient `γ` satisfy `γ √a₀ ≥ 17` (so the balancing set of every nonbase call
has more than `17` points), let `sel` be a valid separator rule (minimum balancing square, `t ∈ [1, 3]`, no
vertex on the separator's boundary) and `tie` an injective tie rule. Then for every well-formed state `S` on
`Γ`, with arbitrary edge weights `S.w`, the family `MixedRepr(S)` (Algorithm 2, run with fuel `|V| + 1`)
dominates packing-compliant covers in the sense of Definition 5.1: each member is a feasible cover of `S`,
and for every feasible cover `C` whose free edges are packing-compliant and every external matching `X`
compatible with `C` some member `R` has `w(R) ≤ w(C)` and `M(R) ∪ X` connected.

**Formalization Note** The page's `a₀`, `γ`, selection rule and tie rule enter as parameters, and the
statement holds for every choice satisfying the hypotheses, which include the page's ("Choose a0 > 17
sufficiently large and γ as in equation (15)", p.11; "Increasing constants if necessary ensures that the
chosen balancing set always has more than seventeen points on a nonbase call", p.11). The fuel `|V| + 1`
suffices because every split is balanced; fuel `0` is a junk value and is never used. -/
theorem lemma_5_4 (n m : ℕ) (hn : 3 ≤ n) (P : Fin n → Pt) (hP : GeneralPos P) (Γ : Skeleton n m)
    (hΓ : IsConvexSkeleton P Γ) (a0 : ℕ) (ha0 : 17 < a0) (γ : ℝ)
    (hγ : 17 ≤ γ * Real.sqrt (a0 : ℝ)) (sel : Selector n m) (hsel : IsValidSelector P Γ sel)
    (tie : Finset (Edge n m) → ℕ) (htie : Function.Injective tie) (S : State n m)
    (hS : IsState Γ S) :
    Dominates P Γ S (mixedRepr P Γ a0 γ sel tie (S.V.card + 1) S) := by sorry

end FewInnerTSP
