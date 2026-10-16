-- Prove2me | Theorems.Thm_ContextualAuctions_Existence_lemma_4
-- name    : ContextualAuctions.Existence.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T19:30:00.925805+00:00
-- url     : https://prove2.me/theorems/56771c35-ef9f-4971-a7cb-39ef6f28c55d
-- title:
--   Lemma 4, p. 10 — X₀ is nonempty, compact and convex in L₁(Θ); f is continuous; C*₀ is upper hemicontinuous with nonempty convex compact values
-- statement:
--   Work in the contextual first price auction model with budgets (see the `Setting` and `FixedPoint` modules), under its standing assumptions, and regard $\mathcal X_0$ as a subset of the Banach space $L_1(\Theta)$ (Lebesgue measure, norm topology). Then:
--
--   1. $\mathcal X_0$ is nonempty, compact, and convex as a subset of $L_1(\Theta)$;
--   2. $f:\mathcal X_0\times\mathcal X_0\to\mathbb R$ is continuous when $\mathcal X_0\times\mathcal X_0$ is endowed with the product topology;
--   3. $C^*_0:\mathcal X_0\rightrightarrows\mathcal X_0$, $C^*_0(\mu)=\arg\min_{\hat\mu\in\mathcal X_0}f(\mu,\hat\mu)$, is upper hemicontinuous with nonempty, convex and compact values.
--
--   These are the hypotheses of the Kakutani–Fan–Glicksberg fixed-point theorem for $C^*_0$ on $\mathcal X_0$.
--
--   **Formalization Note** The statement is about a.e.-classes: $\mathcal X_0$ is replaced by the set of classes in $L_1(\Theta)$ with a representative in $\mathcal X_0$, and $f$ and $C^*_0$ are evaluated on representatives (they do not depend on the choice). Upper hemicontinuity is Mathlib's `UpperHemicontinuousOn`: every neighbourhood of $C^*_0(g)$ is a neighbourhood of $C^*_0(g')$ for $g'\in\mathcal X_0$ near $g$.
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science, Articles in Advance (2023), doi:10.1287/mnsc.2023.4719, p. 10, Lemma 4

import Mathlib
import Definitions.Def_ContextualAuctions_Existence_Setting
import Definitions.Def_ContextualAuctions_Existence_FixedPoint

namespace ContextualAuctions.Existence

theorem lemma_4 (M : Model) (hM : M.Standing) :
    ((X0L M).Nonempty ∧ IsCompact (X0L M) ∧ Convex ℝ (X0L M)) ∧
      ContinuousOn (fun p : L1Theta M × L1Theta M => fL M p.1 p.2) (X0L M ×ˢ X0L M) ∧
      (UpperHemicontinuousOn (C0starL M) (X0L M) ∧
        ∀ g ∈ X0L M, (C0starL M g).Nonempty ∧ Convex ℝ (C0starL M g) ∧
          IsCompact (C0starL M g)) := by sorry

end ContextualAuctions.Existence
