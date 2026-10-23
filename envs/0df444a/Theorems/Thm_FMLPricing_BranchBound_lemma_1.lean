-- Prove2me | Theorems.Thm_FMLPricing_BranchBound_lemma_1
-- name    : FMLPricing.BranchBound.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:35:40.319783+00:00
-- url     : https://prove2.me/theorems/cf3bca95-c14f-48e5-83bf-60fa63943fd7
-- title:
--   Lemma 1, p. 11 — with no-purchase probabilities fixed at x ∈ X, revenue maximization over prices is the concave program cnstr-rev(x)
-- statement:
--   Let $x \in X$, the set of no-purchase vectors $q_0(p)$ attained by prices $p \in [\underline p, \bar p]$. Write $T(p) = (e^{-p_j b_j})_{j \in N}$. Then:
--
--   1. $T$ is a bijection from $\{p \in [\underline p, \bar p] : q_{c0}(p) = x_c \text{ for all } c \in M\}$ onto the feasible set of $\texttt{cnstr-rev}(x)$,
--   $$
--   \Big\{ z \in [\underline z, \bar z] : 1 + \sum_{j \in N} s_{cj} z_j = \frac{1}{x_c} \text{ for all } c \in M \Big\};
--   $$
--   2. on that price set, $\Pi(p) = -\sum_{j \in N} z_j \log(z_j)\, k_j^\top x$ with $z = T(p)$;
--   3. the objective $z \mapsto -\sum_{j} z_j \log(z_j)\, k_j^\top x$ is concave on $[\underline z, \bar z]$.
--
--   Together these say that maximizing $\Pi$ over $[\underline p, \bar p]$ subject to $q_{c0}(p) = x_c$ for all $c$ is equivalent to $\texttt{cnstr-rev}(x)$, a concave maximization problem with linear constraints. This lets $\pi(x)$ be computed by convex optimization.
--
--   **Formalization Note** "Is equivalent to" is encoded as the bijection of feasible sets together with the equality of objectives. The constraints of $\texttt{cnstr-rev}(x)$ are linear by inspection, so only concavity is stated.
-- source:
--   van de Geer & den Boer, Price Optimization Under the Finite-Mixture Logit Model, SSRN 3235432 (version of August 26, 2021), p. 11, Lemma 1 (proof p. 33)

import Mathlib
import Definitions.Def_FMLPricing_BranchBound_Model

namespace FMLPricing.BranchBound

/-- Lemma 1, p. 11: for `x ∈ X`, the change of variables `z_j = e^{−p_j b_j}` maps the
prices `p ∈ [p̲, p̄]` with `q_0(p) = x` bijectively onto the feasible set of
`cnstr-rev(x)`, carries `Π` to its objective, and that objective is concave on
`[z̲, z̄]`. -/
theorem lemma_1 {m n : ℕ} (I : FML m n) (hI : Standing I) (x : Fin m → ℝ) (hx : x ∈ Xset I) :
    Set.BijOn (zOf I) {p | p ∈ priceBox I ∧ ∀ c, q0 I p c = x c} (cnstrFeasible I x) ∧
      (∀ p ∈ priceBox I, (∀ c, q0 I p c = x c) → Pi I p = cnstrObj I x (zOf I p)) ∧
      ConcaveOn ℝ (Set.Icc (zLo I) (zHi I)) (cnstrObj I x) := by sorry

end FMLPricing.BranchBound
