-- Prove2me | Theorems.Thm_Finset_ruzsa_sumset_to_difference
-- name    : Finset.ruzsa_sumset_to_difference
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-17T06:31:23.533638+00:00
-- url     : https://prove2.me/theorems/4d7f76ef-eff4-49f1-b01a-bf8f22e655aa
-- title:
--   Plünnecke–Ruzsa with the Ruzsa triangle inequality: small sumset implies small difference set
-- statement:
--   Let $G$ be an additive commutative group and let $K > 0$, $c > 0$. Let $A, B \subseteq G$ be nonempty finite sets with
--   $$|A + B| \le K\,|A| \qquad\text{and}\qquad |B| \ge c\,|A|.$$
--   Then the difference set satisfies
--   $$|A - B| \le \tfrac{K^3}{c}\,|A|.$$
--
--   The proof is ordinary Ruzsa calculus, in two moves, and owes nothing to the Balog-Szemeredi-Gowers literature. First the Plunnecke-Ruzsa inequality (Mathlib's `Finset.pluennecke_ruzsa_inequality_nsmul_add`, in the form $|2 \cdot B| \le (|A+B|/|A|)^2|A|$) upgrades the hypothesis $|A+B| \le K|A|$ to
--   $$|B + B| \le K^2\,|A|.$$
--   Then the Ruzsa triangle inequality (`Finset.ruzsa_triangle_inequality_sub_add_add`) gives
--   $$|A - B|\,|B| \le |A + B|\,|B + B| \le K^3\,|A|^2,$$
--   and the relative-density hypothesis $c|A| \le |B|$ finishes by division.
--
--   In the Balog-Szemeredi-Gowers project this is the last step, converting the graph step's output — a bound on the honest sum $|A' + B'|$ — into the stated bound on the difference set $|A' - B'|$, at the cost of cubing $K$ and dividing by the relative density $c$.
-- source:
--   Plunnecke-Ruzsa inequality composed with the Ruzsa triangle inequality; proved here via Mathlib's Finset.pluennecke_ruzsa_inequality_nsmul_add. NOT stated in any of the Balog-Szemeredi, Gowers, Fox-Sudakov or Tao-Vu BSG arguments. See Petridis, New proofs of Plunnecke-type estimates for product sets in groups, Combinatorica 32 (2012) 721-733, arXiv:1101.3507. Formalized in https://github.com/mysticflounder/lean-formalizations/blob/dd46c17a2a034d7bfa0df02e7f77834d35592864/lean/LeanFormalizations/Combinatorics/Additive/BalogSzemerediGowers.lean#L593-L672

import Mathlib

open scoped Pointwise

theorem Finset.ruzsa_sumset_to_difference {G : Type*} [AddCommGroup G] [DecidableEq G] :
    ∀ K c : ℝ, 0 < K → 0 < c → ∀ A B : Finset G, A.Nonempty → B.Nonempty →
      ((A + B).card : ℝ) ≤ K * A.card →
      c * (A.card : ℝ) ≤ (B.card : ℝ) →
      ((A - B).card : ℝ) ≤ K ^ 3 / c * A.card := by sorry
