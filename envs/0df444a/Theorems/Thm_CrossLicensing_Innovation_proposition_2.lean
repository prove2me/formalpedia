-- Prove2me | Theorems.Thm_CrossLicensing_Innovation_proposition_2
-- name    : CrossLicensing.Innovation.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T13:01:31.600854+00:00
-- url     : https://prove2.me/theorems/c31ec2ce-aefd-4ff2-ade1-0526b23416e4
-- title:
--   Proposition 2, p. 12 — every innovation equilibrium is a duopoly; T*(β) is an equilibrium, boundary if k2 < k̂2(k1|β), interior otherwise
-- statement:
--   Assume $0 \le \beta \le 1$ and $49/144 < k_2 < k_1$. In the innovation game, manufacturer $M_i$ chooses $T_i \ge 0$ and earns $\Pi^*_i(T_1, T_2\mid\beta) - k_iT_i^2$, where $\Pi^*_i$ is its Cournot profit at the supplier's optimal wholesale price (the least maximizer of $r(q_1 + q_2)$ over $r \ge 0$). Let $T^*(\beta) = (T^B_1, T^B_2)$ if $k_2 < \hat k_2(k_1\mid\beta)$ and $T^*(\beta) = (T^I_1, T^I_2)$ otherwise, with the closed forms of the proof. Then:
--
--   1. **every** pure Nash equilibrium of the innovation game is a downstream duopoly (both manufacturers sell a positive quantity);
--   2. $T^*_1(\beta), T^*_2(\beta) \ge 0$, the profile $T^*(\beta)$ is a pure Nash equilibrium, and it is a duopoly;
--   3. **(boundary duopoly)** if $k_2 < \hat k_2(k_1\mid\beta)$, then $\beta < \sqrt3 - 1$, $T^*(\beta) = (T^B_1, T^B_2)$ and the superior manufacturer invests exactly up to the duopoly boundary:
--   $$T^*_2 = \hat T_2(T^*_1\mid\beta);$$
--   4. **(interior duopoly)** if $k_2 \ge \hat k_2(k_1\mid\beta)$, then $T^*(\beta) = (T^I_1, T^I_2)$ and both first-order conditions hold there:
--   $$\frac{\partial}{\partial T_1}\big[\Pi^d_1(T_1, T^*_2) - k_1T_1^2\big]\Big|_{T^*_1} = 0,\qquad \frac{\partial}{\partial T_2}\big[\Pi^d_2(T^*_1, T_2) - k_2T_2^2\big]\Big|_{T^*_2} = 0,$$
--   with $\Pi^d_i$ Lemma 1's duopoly gross profits.
--
--   Proposition 2 says that a supplier committing to cross-licensing never ends up with a single seller: the superior manufacturer either stops at the boundary where the supplier still prefers a duopoly, or innovates at an unconstrained interior level. Proposition 3 is its instance $\beta = 0$.
--
--   **Formalization Note** The equilibrium is not unique in general (for some parameters a mirrored boundary profile with $M_1$ on its own boundary is also an equilibrium), so the statement asserts that $T^*(\beta)$ is an equilibrium and that every equilibrium is a duopoly, not that $T^*(\beta)$ is the only one. The first-order conditions are taken on Lemma 1's duopoly polynomials, because the game payoff of $M_2$ jumps at $T_2 = \hat T_2$. The paper's "or equivalently $\beta < \hat\beta(k_1, k_2)$" is not formalized; "this region shrinks to empty as $\beta$ increases" is the milestone on $\hat k_2$'s monotonicity.
-- source:
--   Wang, Huang, Lee, Cross-licensing in a Supply Chain with Asymmetric Manufacturers, SSRN 3053682 (version of 2023-04-27), p. 12, Proposition 2; proof pp. A.1–A.2 (PDF 33–34)

import Mathlib
import Definitions.Def_CrossLicensing_Innovation_Model
import Definitions.Def_CrossLicensing_Innovation_ClosedForms

namespace CrossLicensing.Innovation

theorem proposition_2 (β k1 k2 : ℝ) (h : Standing β k1 k2) :
    (∀ T1 T2 : NNReal, IsInnovationEquilibrium β k1 k2 T1 T2 → IsDuopoly β T1 T2) ∧
    (∃ T1 T2 : NNReal, (T1 : ℝ) = Tstar1 β k1 k2 ∧ (T2 : ℝ) = Tstar2 β k1 k2 ∧
      IsInnovationEquilibrium β k1 k2 T1 T2) ∧
    IsDuopoly β (Tstar1 β k1 k2) (Tstar2 β k1 k2) ∧
    (k2 < khat2 β k1 →
      β < Real.sqrt 3 - 1 ∧ Tstar1 β k1 k2 = TB1 β k1 ∧ Tstar2 β k1 k2 = TB2 β k1 ∧
      Tstar2 β k1 k2 = That2 β (Tstar1 β k1 k2)) ∧
    (khat2 β k1 ≤ k2 →
      Tstar1 β k1 k2 = TI1 β k1 k2 ∧ Tstar2 β k1 k2 = TI2 β k1 k2 ∧
      HasDerivAt (fun x => duoGross1 β x (Tstar2 β k1 k2) - k1 * x ^ 2) 0 (Tstar1 β k1 k2) ∧
      HasDerivAt (fun x => duoGross2 β (Tstar1 β k1 k2) x - k2 * x ^ 2) 0 (Tstar2 β k1 k2)) := by sorry

end CrossLicensing.Innovation
