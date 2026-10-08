-- Prove2me | Theorems.Thm_BellmanDP_ExistUnique_type_two_stability
-- name    : BellmanDP.ExistUnique.type_two_stability
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T16:02:44.335902+00:00
-- url     : https://prove2.me/theorems/667d9798-17ba-4fd4-98b7-0d5942b30551
-- title:
--   Chapter IV, Theorem 4 — stability of the solution of a Type Two equation (corrected)
-- statement:
--   Consider two equations of Type Two with the same $h$ and $T$ and with rewards $g$ and $G$, and let $f$, $F$ be their solutions bounded in every finite part of $D$. Let $c$ and $a < 1$ be such that $|h(p,q)| \le a$ for all $q$ and all $p \in D$ with $\|p\| \le c$, and such that $T$ maps $\{p \in D : \|p\| \le c\}$ into $\{\|p\| \le c\}$. With $u(c) = \sup_{p \in D,\ \|p\| \le c}\sup_q |G(p,q) - g(p,q)|$,
--   $$\sup_{p \in D,\ \|p\| \le c} |F(p) - f(p)| \le \frac{u(c)}{1 - a}.$$
--
--   This is the Type Two counterpart of Theorem 3: a geometric factor $1/(1-a)$ replaces the series along the shrinking radii $a^n c$.
--
--   **Formalization Note** The book prints the left side as $|F(p) - (p)|$, a misprint for $|F(p) - f(p)|$. The hypothesis that $T$ keeps the ball of radius $c$ inside itself is added. It holds for every $c$ under the first alternative of Type Two ($\|T(p,q)\| \le \|p\|$), where the statement is the book's. Under the second alternative ($D$ bounded, $T$ arbitrary) the printed bound fails without it. For example, take $N = 1$, $D = [-2,2]$, $T \equiv 2$, $h \equiv 1/2$, $g \equiv 0$, and $G(2,q) = 1$, $G(p,q) = 0$ otherwise. Then $f \equiv 0$ and $F(p) = 1$ for $p \ne 2$, so $|F(0) - f(0)| = 1$, while $u(1)/(1-a) = 0$.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter IV, § 6, Eq. (6.5) and Theorem 4, Eq. (6.8), p. 124

import Mathlib
import Definitions.Def_BellmanDP_ExistUnique_SupEquation
import Definitions.Def_BellmanDP_ExistUnique_EquationTypes

namespace BellmanDP.ExistUnique

/-- Bellman, *Dynamic Programming*, Ch. IV, § 6, Theorem 4, p. 124 (corrected). Let
`f(p) = Sup_q [g + h f(T)]` and `F(p) = Sup_q [G + h F(T)]` both be of Type Two (same `h`, `T`),
with solutions `f`, `F` bounded in every finite part of `D`. Let `c` be such that `|h| ≤ a < 1`
on `{p ∈ D : ‖p‖ ≤ c}` and `T` maps that set into `‖·‖ ≤ c` (automatic for every `c` under the
first alternative `‖T(p, q)‖ ≤ ‖p‖` of Type Two). Then
`Sup_{‖p‖ ≤ c} |F(p) − f(p)| ≤ u(c)/(1 − a)`, `u(c) = Sup_{‖p‖ ≤ c} Sup_q |G(p, q) − g(p, q)|`.
The ball-invariance hypothesis is added to the printed statement, which fails without it
under the bounded-domain alternative. -/
theorem type_two_stability {N : ℕ} {S : Type*} [Nonempty S]
    (D : Set (EuclideanSpace ℝ (Fin N))) (g G h : EuclideanSpace ℝ (Fin N) → S → ℝ)
    (T : EuclideanSpace ℝ (Fin N) → S → EuclideanSpace ℝ (Fin N))
    (hg : TypeTwo D g h T) (hG : TypeTwo D G h T)
    (f F : EuclideanSpace ℝ (Fin N) → ℝ)
    (hf_bdd : BoundedOnBoundedParts D f) (hf : ∀ p ∈ D, SolvesAt g h T f p)
    (hF_bdd : BoundedOnBoundedParts D F) (hF : ∀ p ∈ D, SolvesAt G h T F p)
    (c a : ℝ) (ha : a < 1) (hh : ∀ p ∈ D, ‖p‖ ≤ c → ∀ q : S, |h p q| ≤ a)
    (hTc : ∀ p ∈ D, ‖p‖ ≤ c → ∀ q : S, ‖T p q‖ ≤ c) :
    ∀ p ∈ D, ‖p‖ ≤ c →
      |F p - f p| ≤ radialSup D (fun p q => G p q - g p q) c / (1 - a) := by sorry

end BellmanDP.ExistUnique
