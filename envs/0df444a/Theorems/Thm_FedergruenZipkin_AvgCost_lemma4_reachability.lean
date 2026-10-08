-- Prove2me | Theorems.Thm_FedergruenZipkin_AvgCost_lemma4_reachability
-- name    : FedergruenZipkin.AvgCost.lemma4_reachability
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:38:22.016984+00:00
-- url     : https://prove2.me/theorems/58631987-e107-45eb-8143-46b3df304856
-- title:
--   Lemma 4 (p. 201) — every $x'$ in $[L, U-D_-]$ is reachable from all of $[L, U-D_-]$ under some $\delta\in\Delta_L$
-- statement:
--   In the capacitated inventory model with finite storage capacity $U$, let $L < U - b$. Let $D_-$ and $D_+$ be the smallest and second smallest values $j$ with $p(j) > 0$, and assume $L$ is small enough that
--   $$U - L \ge \max\{b,\ D_- + D_+\}.$$
--
--   **Lemma 4.** For every $x'$ with $L \le x' \le U - D_-$ there is a policy $\delta \in \Delta_L$ (feasible, and ordering to capacity whenever $x \le L$) such that, for all $x_0$ in $[L, U - D_-]$, the state $x'$ can be reached from $x_0$ under $\delta$ in a finite number of periods: for some $n \ge 0$, $\Pr\{x_n = x' \mid x_0, \delta\} > 0$.
--
--   This irreducibility property is condition FST2(b) in the paper's proof of Theorem 1(a).
--
--   **Formalization Note** $D_-$ and $D_+$ are parameters characterised by hypotheses ($p(D_-) > 0$ and $p(j) = 0$ for $j < D_-$; $D_- < D_+$, $p(D_+) > 0$ and $p(j) = 0$ strictly between them) rather than defined by an infimum; under Assumption 4(b) they exist. The $n$-step probability is the $n$-th power of the transition operator applied to the indicator of $\{x'\}$, and $n = 0$ covers $x_0 = x'$.
-- source:
--   Federgruen and Zipkin, An Inventory Model with Limited Production Capacity and Uncertain Demands I, Math. Oper. Res. 11(2), 1986, p. 201, Lemma 4 (with the definition of D_-, D_+ and the condition on L preceding it)

import Mathlib
import Definitions.Def_FedergruenZipkin_AvgCost_Model

namespace FedergruenZipkin.AvgCost
open scoped ENNReal
theorem lemma4_reachability (M : Model) (U L : ℤ) (Dm Dp : ℕ)
    (hDm : 0 < M.p Dm ∧ ∀ j < Dm, M.p j = 0)
    (hDp : Dm < Dp ∧ 0 < M.p Dp ∧ ∀ j, Dm < j → j < Dp → M.p j = 0)
    (hL : L < U - M.b) (hUL : max (M.b : ℤ) ((Dm : ℤ) + Dp) ≤ U - L) :
    ∀ x' : ℤ, L ≤ x' → x' ≤ U - Dm → ∃ δ : ℤ → ℤ, FeasibleL M U L δ ∧
      ∀ x₀ : ℤ, L ≤ x₀ → x₀ ≤ U - Dm → ∃ n : ℕ, 0 < (P M δ)^[n] (Set.indicator {x'} 1) x₀ := by sorry
end FedergruenZipkin.AvgCost
