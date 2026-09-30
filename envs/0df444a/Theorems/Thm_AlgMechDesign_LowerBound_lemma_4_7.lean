-- Prove2me | Theorems.Thm_AlgMechDesign_LowerBound_lemma_4_7
-- name    : AlgMechDesign.LowerBound.lemma_4_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T18:49:46.113349+00:00
-- url     : https://prove2.me/theorems/a5dfdea9-17c0-4082-b421-11051614692b
-- title:
--   Lemma 4.7 — price-difference inequalities characterizing the allocated set
-- statement:
--   Let $(x,p)$ be a truthful direct mechanism for task scheduling, $t$ a positive type vector, $i$ an agent and $X = x^i(t)$. For disjoint task sets $A,B$ let $\Delta^i(A,B) = p^i(A\cup B,t^{-i}) - p^i(A,t^{-i})$ and $t^i(A) = \sum_{j\in A} t^i_j$. For every set $D \ne X$ that is attainable for $i$ against $t^{-i}$:
--
--   1. if $D \subset X$ then $\Delta^i(D, X-D) \ge t^i(X-D)$;
--   2. if $D \supset X$ then $\Delta^i(X, D-X) \le t^i(D-X)$;
--   3. otherwise, with $L = D\cap X$,
--   $$
--   \Delta^i(L, X-L) - t^i(X-L) \ \ge\ \Delta^i(L, D-L) - t^i(D-L).
--   $$
--
--   Moreover, if an attainable set $Y$ satisfies these inequalities strictly (with $Y$ in place of $X$) for every attainable $D \neq Y$, then $Y = X = x^i(t)$.
--
--   The lemma is used to show that a perturbation of agent 1's type which makes its current bundle strictly better leaves the allocation unchanged (Claim 4.8).
--
--   **Formalization Note** As for Proposition 4.5, $D$ ranges over sets attainable for $i$ against $t^{-i}$ (Definition 12 gives unattainable sets price $0$, and the printed "for each set $D$" fails for them). The "Moreover" part also requires $Y$ attainable, as in its only use ($Y = x^1(t)$). Since $D \ne X$, the paper's $\subset$, $\supset$ are proper inclusions; "otherwise" means neither $D \subseteq X$ nor $X \subseteq D$. The set $X$ is a binder with the hypothesis $X = x^i(t)$.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 178, Notation (price difference) and Lemma 4.7 (proof p. 179)

import Mathlib
import Definitions.Def_AlgMechDesign_LowerBound_Model
import Definitions.Def_AlgMechDesign_LowerBound_Price

namespace AlgMechDesign.LowerBound

/-- Lemma 4.7, over attainable sets: let `X = xⁱ(t)`. For every attainable `D ≠ X`,
(1) if `D ⊂ X` then `Δⁱ(D, X - D) ≥ tⁱ(X - D)`; (2) if `D ⊃ X` then `Δⁱ(X, D - X) ≤ tⁱ(D - X)`;
(3) otherwise, with `L = D ∩ X`, `Δⁱ(L, X - L) - tⁱ(X - L) ≥ Δⁱ(L, D - L) - tⁱ(D - L)`.
Moreover, an attainable `Y` satisfying these inequalities strictly for every attainable `D ≠ Y`
equals `X`. -/
theorem lemma_4_7 {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htruth : IsTruthful alloc pay)
    (t : Fin n → Fin k → ℝ) (ht : IsType t) (i : Fin n)
    (X : Finset (Fin k)) (hX : X = taskSet (alloc t) i) :
    (∀ D : Finset (Fin k), IsAttainable alloc i t D → D ≠ X →
      (D ⊂ X → taskTime (t i) (X \ D) ≤ priceDiff alloc pay i t D (X \ D)) ∧
      (X ⊂ D → priceDiff alloc pay i t X (D \ X) ≤ taskTime (t i) (D \ X)) ∧
      (¬ D ⊆ X → ¬ X ⊆ D →
        priceDiff alloc pay i t (D ∩ X) (D \ (D ∩ X)) - taskTime (t i) (D \ (D ∩ X)) ≤
          priceDiff alloc pay i t (D ∩ X) (X \ (D ∩ X)) - taskTime (t i) (X \ (D ∩ X)))) ∧
    (∀ Y : Finset (Fin k), IsAttainable alloc i t Y →
      (∀ D : Finset (Fin k), IsAttainable alloc i t D → D ≠ Y →
        (D ⊂ Y → taskTime (t i) (Y \ D) < priceDiff alloc pay i t D (Y \ D)) ∧
        (Y ⊂ D → priceDiff alloc pay i t Y (D \ Y) < taskTime (t i) (D \ Y)) ∧
        (¬ D ⊆ Y → ¬ Y ⊆ D →
          priceDiff alloc pay i t (D ∩ Y) (D \ (D ∩ Y)) - taskTime (t i) (D \ (D ∩ Y)) <
            priceDiff alloc pay i t (D ∩ Y) (Y \ (D ∩ Y)) - taskTime (t i) (Y \ (D ∩ Y)))) →
      Y = X) := by sorry

end AlgMechDesign.LowerBound
