-- Prove2me | Theorems.Thm_ConstrNestedLogit_Stitch_revenue_characterization
-- name    : ConstrNestedLogit.Stitch.revenue_characterization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:03:15.018813+00:00
-- url     : https://prove2.me/theorems/439dc946-8847-43ba-9ef7-7125a308f6e5
-- title:
--   Revenue characterized by the balance equation
-- statement:
--   Fix an assortment $S=(S_i)_{i\in M}$ and a real number $z$. With $V_i(S_i)$, $R_i(S_i)$, $\gamma_i$, and $v_0$ as in the nested logit model, the balance equation holds exactly when $z$ equals the expected revenue $\Pi(S)$. Its inequality form holds exactly when $z$ bounds that revenue from above:
--
--   $$
--   v_0z=\sum_{i\in M}V_i(S_i)^{\gamma_i}(R_i(S_i)-z)\quad\Longleftrightarrow\quad z=\Pi(S),
--   $$
--   $$
--   v_0z\ge\sum_{i\in M}V_i(S_i)^{\gamma_i}(R_i(S_i)-z)\quad\Longleftrightarrow\quad \Pi(S)\le z.
--   $$
--
--   The two relations express the algebraic conversion used in the proof of Lemma 1 to compare candidate combinations with the value solving equation (2).
--
--   **Formalization Note** This is the main model with $v_{i0}=0$, $v_0>0$, positive product weights, and $\gamma_i\in(0,1]$. The formulas include empty assortments, for which $R_i(\varnothing)=0$.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, pp. 11–12, proof of Lemma 1

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model

namespace ConstrNestedLogit.Stitch

/-- The algebraic equalities and inequality used in the proof of Lemma 1, pp. 11–12. -/
theorem revenue_characterization {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n)
    (S : ι → Finset (Fin n)) (z : ℝ)
    (hvnp : ∀ i, I.vnp i = 0)
    (hv0 : 0 < I.v0)
    (hv : ∀ i j, 0 < I.v i j)
    (hγ : ∀ i, 0 < I.γ i ∧ I.γ i ≤ 1) :
    (I.v0 * z = ∑ i, NestedLogitVariants.LP.nestWeight I i (S i) *
      (NestedLogitVariants.LP.R I i (S i) - z) ↔
      z = NestedLogitVariants.LP.revenue I S) ∧
    (I.v0 * z ≥ ∑ i, NestedLogitVariants.LP.nestWeight I i (S i) *
      (NestedLogitVariants.LP.R I i (S i) - z) ↔
      NestedLogitVariants.LP.revenue I S ≤ z) := by sorry

end ConstrNestedLogit.Stitch
