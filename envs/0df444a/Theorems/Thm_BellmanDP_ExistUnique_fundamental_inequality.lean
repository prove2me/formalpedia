-- Prove2me | Theorems.Thm_BellmanDP_ExistUnique_fundamental_inequality
-- name    : BellmanDP.ExistUnique.fundamental_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T15:29:06.370541+00:00
-- url     : https://prove2.me/theorems/b71f446a-6cd4-46de-92dd-4eb4c62c83ae
-- title:
--   Chapter IV, Lemma 1 — the fundamental inequality for two supremum transformations
-- statement:
--   Fix a state $p$, a set $D \subseteq \mathbb{R}^N$ and, for each decision $q \in S$, a nonnegative measure $dG(p,q,\cdot)$ on $\mathbb{R}^N$. For functions $f_1, F_1$ integrable over $D$ against every $dG(p,q,\cdot)$ put
--   $$S_1(f_1,p,q) = g(p,q) + \int_{r \in D} f_1(r)\,dG(p,q,r), \qquad S_2(F_1,p,q) = h(p,q) + \int_{r \in D} F_1(r)\,dG(p,q,r),$$
--   and let $f_2(p) = \sup_q S_1(f_1,p,q)$ and $F_2(p) = \sup_q S_2(F_1,p,q)$, both finite suprema. Then
--   $$|f_2(p) - F_2(p)| \le \sup_q\Big[\,|g(p,q) - h(p,q)| + \int_{r \in D} |f_1(r) - F_1(r)|\,dG(p,q,r)\Big].$$
--
--   The inequality compares two supremum transformations without any information on where the suprema are attained. Every existence, uniqueness and stability argument of the chapter rests on it.
--
--   **Formalization Note** The measures are `Measure (EuclideanSpace ℝ (Fin N))` indexed by $q$, and the integrals are over $D$. The suprema $f_2(p)$, $F_2(p)$ are encoded with `IsLUB`. The right-hand supremum may be $+\infty$, so the conclusion is stated as: every real $M$ bounding the bracket for all $q$ bounds $|f_2(p) - F_2(p)|$. Here $h$ is the second reward function of $S_2$, not the multiplier of Eq. (1.1). The book's applications take $\int f\,dG = h(p,q) f(T(p,q))$, which is a nonnegative measure only when $h \ge 0$.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter IV, § 2, Eqs. (2.1)-(2.2) and Lemma 1, Eq. (2.3), pp. 117-118

import Mathlib

open MeasureTheory

namespace BellmanDP.ExistUnique

/-- Bellman, *Dynamic Programming*, Ch. IV, § 2, Lemma 1, p. 118 (fundamental inequality).
Fix a state `p` and nonnegative measures `dG(p, q, ·)` on `ℝ^N` (`q ∈ S`). Let
`S₁(f₁, p, q) = g(p, q) + ∫_{r ∈ D} f₁(r) dG(p, q, r)` and
`S₂(F₁, p, q) = h(p, q) + ∫_{r ∈ D} F₁(r) dG(p, q, r)`, and let `f₂(p) = Sup_q S₁`,
`F₂(p) = Sup_q S₂` (genuine suprema). Then
`|f₂(p) − F₂(p)| ≤ Sup_q [|g(p, q) − h(p, q)| + ∫_{r ∈ D} |f₁(r) − F₁(r)| dG(p, q, r)]`,
stated as: every upper bound `M` of the bracket over `q` bounds `|f₂(p) − F₂(p)|`. -/
theorem fundamental_inequality {N : ℕ} {S : Type*}
    (D : Set (EuclideanSpace ℝ (Fin N))) (p : EuclideanSpace ℝ (Fin N))
    (G : EuclideanSpace ℝ (Fin N) → S → Measure (EuclideanSpace ℝ (Fin N)))
    (g h : EuclideanSpace ℝ (Fin N) → S → ℝ) (f₁ F₁ : EuclideanSpace ℝ (Fin N) → ℝ)
    (hf₁ : ∀ q : S, IntegrableOn f₁ D (G p q)) (hF₁ : ∀ q : S, IntegrableOn F₁ D (G p q))
    (f₂ F₂ : EuclideanSpace ℝ (Fin N) → ℝ)
    (hf₂ : IsLUB (Set.range fun q : S => g p q + ∫ r in D, f₁ r ∂(G p q)) (f₂ p))
    (hF₂ : IsLUB (Set.range fun q : S => h p q + ∫ r in D, F₁ r ∂(G p q)) (F₂ p))
    (M : ℝ) (hM : ∀ q : S, |g p q - h p q| + ∫ r in D, |f₁ r - F₁ r| ∂(G p q) ≤ M) :
    |f₂ p - F₂ p| ≤ M := by sorry

end BellmanDP.ExistUnique
