-- Prove2me | Theorems.Thm_BBDisclosure_Total_proposition_3a
-- name    : BBDisclosure.Total.proposition_3a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:24:13.348585+00:00
-- url     : https://prove2.me/theorems/12a413ee-5e40-4e0a-9229-af6992d5dab7
-- title:
--   Proposition 3(a), p. 8520 — BBD raises (lowers) firms' total profits when $c>c_l$ ($c<c_l$)
-- statement:
--   Zhang and Li, Proposition 3: "Compared with uniform disclosure, there exists cutoff points, $c_l$ and $c_m$, such that a. BBD increases (decreases) firms' total profits when $c>c_l$ ($c<c_l$)."
--
--   Formally: there is a cutoff $c_l\in(0,5/36)$ such that for every unit disclosure cost $0<c<5/36$,
--   1. the two-period game has a symmetric subgame-perfect equilibrium under uniform disclosure and one under behavior-based disclosure (BBD);
--   2. for every symmetric subgame-perfect equilibrium under uniform disclosure, with total profits $\Pi^{*,U}_a,\Pi^{*,U}_b$, and every one under BBD, with total profits $\Pi^{*,BBD}_a,\Pi^{*,BBD}_b$,
--   $$c>c_l\;\Longrightarrow\;\Pi^{*,U}_i<\Pi^{*,BBD}_i,\qquad c<c_l\;\Longrightarrow\;\Pi^{*,BBD}_i<\Pi^{*,U}_i\qquad(i=a,b).$$
--
--   Behavior-based disclosure always raises second-period profits (Proposition 1(c)), but its effect on first-period competition depends on the disclosure cost; this result says the total effect over both periods changes sign exactly across one cutoff.
--
--   **Formalization Note.** Parts (b) and (c) of Proposition 3 (consumer surplus, social welfare) are not stated: the paper defines these quantities only through their Table 1 values. The cutoff is quantified before $c$ and the equilibria and lies strictly inside $(0,5/36)$; nothing is claimed at $c=c_l$. Equilibria are symmetric and subgame perfect, with global first-period deviations and second-period equilibrium play at every share. The existence clauses keep the comparison from being vacuous.
-- source:
--   Zhang and Li, Retention or Acquisition? Behavior-Based Quality Disclosure, Management Sci. 71(10) (2025) 8510–8525, DOI 10.1287/mnsc.2022.01081, p. 8520, Proposition 3 (lead-in and part a)

import Mathlib
import Definitions.Def_BBDisclosure_Total_Stage2
import Definitions.Def_BBDisclosure_Total_Game

namespace BBDisclosure.Total

/-- Proposition 3(a), p. 8520: there is a cutoff `c_l ∈ (0, 5/36)` such that, for every disclosure
cost `c ∈ (0, 5/36)`, symmetric subgame-perfect equilibria exist under both regimes, and
behavior-based disclosure raises both firms' total two-period profits relative to uniform
disclosure when `c > c_l`, and lowers them when `c < c_l`. -/
theorem proposition_3a :
    ∃ cl : ℝ, 0 < cl ∧ cl < 5 / 36 ∧
      ∀ c : ℝ, 0 < c → c < 5 / 36 →
        (∃ s : SPE_U, IsSymSPE_U c s) ∧ (∃ s : SPE_BBD, IsSymSPE_BBD c s) ∧
        ∀ (sU : SPE_U) (sB : SPE_BBD), IsSymSPE_U c sU → IsSymSPE_BBD c sB →
          (cl < c → totalA_U c sU < totalA_BBD c sB ∧ totalB_U c sU < totalB_BBD c sB) ∧
          (c < cl → totalA_BBD c sB < totalA_U c sU ∧ totalB_BBD c sB < totalB_U c sU) := by sorry

end BBDisclosure.Total
