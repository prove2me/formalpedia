-- Prove2me | Theorems.Thm_FengLiYangMatching_General_conditional_local_experiment
-- name    : FengLiYangMatching.General.conditional_local_experiment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T20:30:03.490175+00:00
-- url     : https://prove2.me/theorems/eaa70581-3396-49df-832e-de7e18acc117
-- title:
--   Conditional recovery as a finite coupled experiment
-- statement:
--   Fix the source's admissible phase parameters, a finite simple graph, and an analysis-only maximum matching. For almost every accepted-edge history $H_b$, fix an early shadow edge $e$ with arrival time $s$, and a background graph $B$ whose conditioning event has positive probability. Let $Y$ be the shadow-unmatched vertices and let the potential edges be all graph edges joining the endpoints of $e$ to $Y$. The marked vertices are the reference vertices of $e$.
--
--   The resulting finite local data satisfy the source's validity and distinct reference-partner conditions. With
--
--   $$
--   q=\frac{1-b}{1-s},\qquad \frac58\le q\le1,
--   $$
--
--   the conditional continuous-time coupled score has exactly the finite experiment's expectation:
--
--   $$
--   \mathbb E[3N+2R+K\mid H_b,B]
--   =\mathbb E_{\sigma,\mathrm{retention}}[3N+2R+K].
--   $$
--
--   On the right, one common uniform order of all base and potential edges is used by both Greedy runs, and the potential edges have independent retention probability $q$. This identifies the actual conditional law with the equivalent formulation preceding Equation (10).
-- source:
--   Feng, Li, Yang, Improved Bounds for Online Matching with Random Edge Arrivals, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1018.pdf, Section 4.1, p. 13, equivalent formulation of the coupled matchings and Equation (10); Sections 4.2–4.3, pp. 14–16.

import Definitions.Def_FengLiYangMatching_General_Local
open MeasureTheory Finset

namespace FengLiYangMatching.General
theorem conditional_local_experiment {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n)
    (hMG : M ⊆ graphEdges G) (hM : IsMatching M) (hmax : M.card = OPT G)
    (a b p : ℝ) (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 3/8) (hp0 : 0 ≤ p) (hp2 : p ≤ 2/3) :
    ∀ᵐ h ∂historyLaw G b, ∀ e ∈ early a h, ∀ B : EdgeSet n,
      0 < conditionalLaw G b p h {w | background G a b h e w = B} →
      let d : Local n := {
        base := B
        potential := (graphEdges G).filter (fun f => ∃ x y, f = s(x,y) ∧ x ∈ e ∧ y ∈ Yset h)
        x1 := e.out.1
        x2 := e.out.2
        Y := Yset h
        marked := references M h e }
      let q : ℝ := (1-b)/(1-h.time e)
      d.Valid ∧ d.Partners ∧ 5/8 ≤ q ∧ q ≤ 1 ∧
        (∫ w, coupledScore G M a b h e w ∂backgroundLaw G a b p h e B) =
          localMean d q (fun σ r => 3*N d σ r+2*R d σ r+K d σ) := by sorry

end FengLiYangMatching.General
