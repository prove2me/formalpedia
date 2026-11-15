-- Prove2me | Theorems.Thm_FengLiYangMatching_General_Supplement_theorem_1_2
-- name    : FengLiYangMatching.General.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:22:54.605712+00:00
-- url     : https://prove2.me/theorems/b2989042-971e-4ade-8ac7-c99b8c96ee32
-- title:
--   Theorem 1.2 — Triangle-free lower bound: 0.5535
-- statement:
--   On every finite triangle-free simple graph $G$, Algorithm 1 with $a=3/32$, $b=4/11$, $p=11/25$ has an integrable output size and satisfies
--
--   $$\mathbb E[\mathrm{ALG}]\ge\frac{1107}{2000}\,\mathrm{OPT}(G).$$
--
--   The same rule works for every graph, without being given the graph or its edge count. Every prefix accepts a matching of observed edges and previously accepted edges remain accepted. These feasibility and irrevocability clauses are included for the concrete witness. Bipartite graphs are included because they are triangle-free; the statement covers all triangle-free graphs, including empty graphs and zero-optimum instances. This is the paper's companion lower bound.
--
--   Differences from the source:
--   - encoding: arbitrary finite labelled vertex set → Fin n and unordered Sym2 edges, for every natural n; reason: every finite simple graph has such a labelling; the representation removes no instance
--   - encoding: there exists a 0.5535-competitive algorithm → the published Algorithm 1 run at the exact Appendix B parameters, with prefix feasibility, irrevocability, integrability and the uniform 1107/2000 guarantee; reason: the source supplies this witness; the extra clauses expose its online-algorithm obligations rather than assume them
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, Improved Bounds for Online Matching with Random Edge Arrivals, STOC 2027 submission #1018 (October 2026), Theorem 1.2, p. 3 (proof: Appendix B, pp. 26–28).

import Definitions.Def_FengLiYangMatching_General_Process

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false

namespace FengLiYangMatching.General.Supplement

/-- Theorem 1.2 with the Algorithm 1 witness of Appendix B. -/
theorem theorem_1_2 :
    (∀ n : ℕ, ∀ l : List (Edge n × ℝ × Bool),
      (l.map (fun o => o.1)).Nodup →
      (l.map (fun o => o.2.1)).Pairwise (· ≤ ·) →
      (∀ o ∈ l, ¬ o.1.IsDiag ∧ o.2.1 ∈ Set.Icc (0 : ℝ) 1) →
      ∀ j ≤ l.length,
        IsMatching (run (3/32) (4/11) (l.take j)).actual ∧
        (run (3/32) (4/11) (l.take j)).actual ⊆
          ((l.take j).map (fun o => o.1)).toFinset) ∧
    (∀ n : ℕ, ∀ l : List (Edge n × ℝ × Bool),
      ∀ j k : ℕ, j ≤ k → k ≤ l.length →
        (run (3/32) (4/11) (l.take j)).actual ⊆
          (run (3/32) (4/11) (l.take k)).actual) ∧
    (∀ n : ℕ, ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 →
      Integrable (ALG G (3/32) (4/11)) (sampleLaw G (11/25)) ∧
      (∫ w, ALG G (3/32) (4/11) w ∂sampleLaw G (11/25)) ≥
        (1107/2000 : ℝ) * (OPT G : ℝ)) := by sorry

end FengLiYangMatching.General.Supplement
