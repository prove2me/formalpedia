-- Prove2me | Theorems.Thm_BundleShaping_NoOrderSet_theorem_2
-- name    : BundleShaping.NoOrderSet.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:12:11.610112+00:00
-- url     : https://prove2.me/theorems/b0fcdf05-acec-4ede-aef5-f562e6f729b2
-- title:
--   Theorem 2, p. 23 — BTS: V_{t+1} concave non-increasing, G_t jointly concave, optimal policy is order-up-to Az*(∅) or dictated by a no-order set via (14)
-- statement:
--   Consider the bundle-to-stock model under the standing assumptions, a period $1\le t\le T$ and an initial net inventory of items $x\in\mathbb R^I$. Then:
--
--   1. **(a)** $V_{t+1}$ is jointly concave and non-increasing on $\mathbb R^I$.
--   2. **(b)** $G_t(y,z,q)$ is jointly concave in $(y,z,q)$ on $\mathbb R^I\times\mathbb R^J\times\Omega$; and, under the coercivity conditions, problem (14) with $I^+=\emptyset$,
--   $$\max\{G_t(Az,z,q): z\in\mathbb R^J,\ q\in\Omega\},$$
--   has at least one maximizer $(y^*_t(\emptyset),z^*_t(\emptyset),q^*_t(\emptyset))=(Az^*,z^*,q^*)$.
--   3. **(c)** If $(Az^*,z^*,q^*)$ is any maximizer of (14) with $I^+=\emptyset$ and $x\le Az^*$, then it is optimal in (9) to produce $z^*$ bundles and order items up to $Az^*$, and $G_t(Az^*,z^*,q^*)=V_t(x)$. Otherwise — that is, under the coercivity conditions, when no maximizer of (14) with $I^+=\emptyset$ satisfies $x\le Az^*$ — there exists a nonempty no-order set $I^+$ and a triple $(y^*,z^*,q^*)$ with $y^*_i=x_i$ for $i\in I^+$ which maximizes (14) for this $I^+$, is optimal in (9), and attains $V_t(x)$. The optimal order-up-to levels, assembly quantities and market shares are thus given by (14), and the optimal bundling strategy is $\{j:q^*_j>0\}$.
--
--   This is the main structural result of the paper: the joint replenishment, assembly and market-share decision is an order-up-to policy, except for a set of overstocked items that are not ordered.
--
--   **Formalization Note.** The coercivity conditions ($\tau_t$ continuous on $\Omega$, $\tilde c^p_{jt}<b^p_{jt}$ and $\tilde c^p_{jt}+\tilde h_{jt}>0$, i.e. the fill rate of §5.2 lies in $(0,1)$) are added, and used only for the existence of a maximizer and for the "otherwise" clause: without them (14) need not attain its supremum. Maximizers need not be unique, so "otherwise" is read as "no maximizer of (14) with $I^+=\emptyset$ has $x\le Az^*$"; reading it against a single fixed maximizer would make the claim false when another maximizer has $x\le Az^*$. Problem (14) keeps the constraint $y\ge Az$. The final sentence on the bundling strategy is the definition of $\mathcal S$ (§3.1) and adds no separate clause. The program (9) is the paper's transformed program (P), stated directly; the change of variables from the original value function (Appendix B) is not formalized.
-- source:
--   Song & Xue, Demand Shaping Through Bundling and Product Configuration, SSRN 3168907 (version of Aug. 19, 2020), p. 23, Theorem 2 (a)–(c)

import Mathlib
import Definitions.Def_BundleShaping_NoOrderSet_Model

namespace BundleShaping.NoOrderSet

open Matrix

variable {I J : Type} [Fintype I] [Fintype J]

theorem theorem_2 (P : Params I J) (hS : P.Standing) (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) :
    (ConcaveOn ℝ Set.univ (P.V (t + 1)) ∧ Antitone (P.V (t + 1))) ∧
    ConcaveOn ℝ (Set.univ ×ˢ Set.univ ×ˢ P.Ω)
      (fun v : (I → ℝ) × (J → ℝ) × (J → ℝ) => P.G t v.1 v.2.1 v.2.2) ∧
    (∀ (x : I → ℝ) (z q : J → ℝ), P.Max14 t ∅ 0 (P.A *ᵥ z) z q → x ≤ P.A *ᵥ z →
      P.Opt9 t x (P.A *ᵥ z) z q ∧ P.G t (P.A *ᵥ z) z q = P.V t x) ∧
    (P.Coercive →
      (∃ (z q : J → ℝ), P.Max14 t ∅ 0 (P.A *ᵥ z) z q) ∧
      ∀ x : I → ℝ, (∀ (z q : J → ℝ), P.Max14 t ∅ 0 (P.A *ᵥ z) z q → ¬ x ≤ P.A *ᵥ z) →
        ∃ S : Finset I, S.Nonempty ∧ ∃ (y : I → ℝ) (z q : J → ℝ),
          P.Max14 t S x y z q ∧ P.Opt9 t x y z q ∧ P.G t y z q = P.V t x) := by sorry

end BundleShaping.NoOrderSet
