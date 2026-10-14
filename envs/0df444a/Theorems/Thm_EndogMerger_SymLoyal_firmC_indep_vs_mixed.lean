-- Prove2me | Theorems.Thm_EndogMerger_SymLoyal_firmC_indep_vs_mixed
-- name    : EndogMerger.SymLoyal.firmC_indep_vs_mixed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:12:02.440206+00:00
-- url     : https://prove2.me/theorems/bb71df46-c338-4c55-9438-ae6f2374287b
-- title:
--   Proof of Proposition 3, PDF p. 49 — Π^(0)_C < Π^(AB)_C for k > k^(AB)_1, and Π^(0)_C = Π^(AB)_C for k < k^(AB)_1
-- statement:
--   Let $0<\alpha<1/3$, $\alpha<k<1-2\alpha$ and $r>0$. Firm $C$'s Table A1 profit without merger, $\Pi^{(0)}_C$, and in the mixed merger, $\Pi^{(AB)}_C$, satisfy
--
--   1. if $k>k^{(AB)}_1(\alpha)$, then $\Pi^{(0)}_C<\Pi^{(AB)}_C$;
--   2. if $k<k^{(AB)}_1(\alpha)$, then
--   $$
--   \Pi^{(0)}_C=\Pi^{(AB)}_C .
--   $$
--
--   **Formalization Note** The paper states part 1 on $\Omega^{(AB)}_1$, which includes $k=k^{(AB)}_1$, where the two profits are equal; part 1 is therefore stated for $k>k^{(AB)}_1$. $\Pi^{(0)}_C$ is the common profit $\Pi^{(0)}_B=\Pi^{(0)}_C$ of Table A1.
-- source:
--   Wang, Wu, Tang & Dai, Endogenous merger decisions among competitors: impact of limited capacity and loyal segments, Management Science (2024), accepted manuscript, Appendix H, proof of Proposition 3, PDF p. 49

import Mathlib
import Definitions.Def_EndogMerger_SymLoyal_Setting
import Definitions.Def_EndogMerger_SymLoyal_Regions

namespace EndogMerger.SymLoyal
theorem firmC_indep_vs_mixed (α k r : ℝ) (hα0 : 0 < α) (hα3 : α < 1 / 3) (hαk : α < k)
    (hk : k < 1 - 2 * α) (hr : 0 < r) :
    (kAB₁ α < k → piIndepB α k r < piABC α k r) ∧
    (k < kAB₁ α → piIndepB α k r = piABC α k r) := by sorry
end EndogMerger.SymLoyal
