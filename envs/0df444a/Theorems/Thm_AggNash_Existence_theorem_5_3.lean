-- Prove2me | Theorems.Thm_AggNash_Existence_theorem_5_3
-- name    : AggNash.Existence.theorem_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:55.124366+00:00
-- url     : https://prove2.me/theorems/ad4d10dd-2750-4d04-afc5-9a87fea189f7
-- title:
--   Theorem 5.3, p. 16 — a game with convex compact action sets, convex l.s.c. costs and equicontinuity in the others' actions has a PNE
-- statement:
--   Consider an $n$-player game in which player $i$ chooses $x_i$ in a set $\mathcal X_i\subset\mathbb R^d$ and incurs the cost $f_i(x_i,x_{-i})$. Suppose that for every player $i$:
--
--   1. $\mathcal X_i$ is a nonempty convex compact subset of $\mathbb R^d$;
--   2. for every $x_{-i}\in\prod_{j\ne i}\mathcal X_j$, the function $f_i(\cdot,x_{-i})$ is convex and lower semicontinuous on $\mathcal X_i$;
--   3. the family $\{f_i(x_i,\cdot):\prod_{j\ne i}\mathcal X_j\to\mathbb R \mid x_i\in\mathcal X_i\}$ is uniformly equicontinuous: for every $\epsilon>0$ there is $\delta>0$ such that $|f_i(x_i,x_{-i})-f_i(x_i,x'_{-i})|\le\epsilon$ for all $x_i\in\mathcal X_i$ whenever $x_{-i},x'_{-i}$ are within $\delta$ of each other (Definition 5.2).
--
--   Then the game admits a pure Nash equilibrium: a profile $x\in\prod_i\mathcal X_i$ with
--
--   $$
--   f_i(x_i,x_{-i})\le f_i(y_i,x_{-i})\qquad\text{for every } i \text{ and every } y_i\in\mathcal X_i.
--   $$
--
--   This extends Rosen's existence theorem from continuous to lower semicontinuous costs in the player's own action. It is what makes the convexified game have an equilibrium (Proposition 2.3).
--
--   **Formalization Note** The cost $f_i$ is a function of the full profile, and $f_i(y_i,x_{-i})$ is its value at `Function.update x i y`. Nonemptiness of $\mathcal X_i$ is added (an empty action set admits no profile). Closeness of $x_{-i}$ and $x'_{-i}$ is measured coordinatewise, $\|x_j-x'_j\|\le\delta$ for all $j\ne i$, instead of in the Euclidean norm of $\prod_{j\ne i}\mathbb R^d$; the two norms are equivalent, so uniform equicontinuity is the same property.
-- source:
--   Liu, Oudjane & Wan, Approximate Nash equilibria in large non-convex aggregative games, arXiv:2011.12604v3, p. 16, Definition 5.2 and Theorem 5.3

import Mathlib
import Definitions.Def_AggNash_Existence_Model

namespace AggNash.Existence

/-- Theorem 5.3 (p. 16), existence of a PNE in l.s.c. convex games. In an `n`-player game with
action sets `Sᵢ ⊂ ℝᵈ` and costs `fᵢ`, suppose for every player `i`: (1) `Sᵢ` is a nonempty
convex compact set; (2) for every `x₋ᵢ ∈ ∏_{j ≠ i} Sⱼ`, `fᵢ(·, x₋ᵢ)` is convex and lower
semicontinuous on `Sᵢ`; (3) the family `{fᵢ(xᵢ, ·) | xᵢ ∈ Sᵢ}` on `∏_{j ≠ i} Sⱼ` is uniformly
equicontinuous (Definition 5.2). Then the game admits a PNE. -/
theorem theorem_5_3 {n d : ℕ} (S : Fin n → Set (E d)) (f : Fin n → (Fin n → E d) → ℝ)
    (hconv : ∀ i, Convex ℝ (S i)) (hcpt : ∀ i, IsCompact (S i)) (hne : ∀ i, (S i).Nonempty)
    (hcvx : ∀ i, ∀ x : Fin n → E d, (∀ j, j ≠ i → x j ∈ S j) →
      ConvexOn ℝ (S i) (fun y => f i (Function.update x i y)))
    (hlsc : ∀ i, ∀ x : Fin n → E d, (∀ j, j ≠ i → x j ∈ S j) →
      LowerSemicontinuousOn (fun y => f i (Function.update x i y)) (S i))
    (hequi : ∀ i, ∀ ε > 0, ∃ δ > 0, ∀ y ∈ S i, ∀ x x' : Fin n → E d,
      (∀ j, j ≠ i → x j ∈ S j) → (∀ j, j ≠ i → x' j ∈ S j) →
      (∀ j, j ≠ i → dist (x j) (x' j) ≤ δ) →
      |f i (Function.update x i y) - f i (Function.update x' i y)| ≤ ε) :
    ∃ x, IsEpsPNE S f 0 x := by sorry

end AggNash.Existence
