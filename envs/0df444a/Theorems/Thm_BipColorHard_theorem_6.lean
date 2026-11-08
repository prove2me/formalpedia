-- Prove2me | Theorems.Thm_BipColorHard_theorem_6
-- name    : BipColorHard.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:35:29.583811+00:00
-- url     : https://prove2.me/theorems/fb2fe167-6c95-4811-a703-5c4fe45b6d4c
-- title:
--   Theorem 6 ([AK00]) — gap MAX-CUT at maximum degree three is NP-hard
-- statement:
--   There is a rational constant $g>0$ such that the following holds. Given a simple graph $F$ of maximum degree at most three and an integer $\tau$, it is NP-hard to decide which of
--   $$\mathrm{MaxCut}(F)\le\tau\quad\text{and}\quad\mathrm{MaxCut}(F)\ge\tau+g|V(F)|$$
--   holds, under the promise that one of them does.
--
--   Precisely, every NP language has a polynomial-time many-one reduction to this promise problem, with the language mapping to the second case and its complement to the first. This is the source of hardness of the whole reduction chain.
--
--   **Formalization Note** The manuscript cites this from the APX-hardness of MAX-CUT on graphs of maximum degree three (Alimonti and Kann, 2000, Theorem 4.2) and does not prove it. It is posed as a milestone and is not assumed by the goal theorem.
--
--   Differences from the source:
--   - reading: "it is NP-hard to decide" → a polynomial-time many-one reduction from every NP language whose image obeys the promise; reason: the proof of Theorem 1 composes a single query from this problem; this reading implies hardness under oracle reductions
--   - reading: graphs $F$ of maximum degree at most three → the image of the reduction has at least one vertex; reason: on the empty graph with $\tau=0$ both cases hold, and a map to it would satisfy the statement trivially; a one-vertex padding excludes it without changing the problem
-- source:
--   Galanis, Guo, He, Štefankovič, Vigoda, NP-hardness for Bipartite Colorings up to the Maximum Degree, manuscript of Nov. 3, 2026 (sha256 78a66d1f…), Theorem 6, p.6 (PDF p.8), citing [AK00, Theorem 4.2]

import Definitions.Def_BipColorHard_Hardness
import Definitions.Def_IIDMatchHard_Cut

set_option autoImplicit false

namespace BipColorHard

open NSWApxHard.Reduction (GraphInput) in
/-- **Theorem 6** ([AK00]), p.6 (PDF p.8), manuscript sha256 78a66d1f…. There is a rational constant `g > 0` such that the following holds. Given a simple graph `F` of maximum degree at
most three and an integer `τ`, it is NP-hard to decide which of `MaxCut(F) ≤ τ` and `MaxCut(F) ≥ τ + g|V(F)|` holds, under the promise that one of them does.

**Formalization Note.** The manuscript cites this from [AK00, Theorem 4.2] and does not prove it; it is posed here as a milestone, not assumed by the goal. "NP-hard" is read as a
polynomial-time many-one reduction from every NP language whose image obeys the promise, with `L` mapping to the large side. The image has at least one vertex: on the graph with no vertices,
`τ = 0` satisfies both cases and the map could not carry any information. -/
theorem theorem_6 :
    ∃ g : ℚ, 0 < g ∧
      ∀ (Sym : Type) [Fintype Sym] [Nonempty Sym] (L : CookPvsNP.Lang Sym), L ∈ CookPvsNP.NP Sym →
        ∃ f : List Sym → GraphInput × ℤ,
          CookPvsNP.PolyTimeComputable (fun x => encGap (f x)) ∧
          ∀ x, 0 < (f x).1.N ∧ MaxDegLe 3 (f x).1 ∧
            (x ∈ L → ((f x).2 : ℝ) + (g : ℝ) * ((f x).1.N : ℝ) ≤ (IIDMatchHard.maxCut (f x).1.G : ℝ)) ∧
            (x ∉ L → (IIDMatchHard.maxCut (f x).1.G : ℝ) ≤ ((f x).2 : ℝ)) := by sorry

end BipColorHard
