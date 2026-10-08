-- Prove2me | Theorems.Thm_ChenSimchiLevi_Additive_kconvex_def22_iff_def21
-- name    : ChenSimchiLevi.Additive.kconvex_def22_iff_def21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:41:06.448372+00:00
-- url     : https://prove2.me/theorems/6f60162e-d48d-43d2-9920-6f7b185c5a83
-- title:
--   Definitions 2.1 and 2.2 of $k$-convexity are equivalent
-- statement:
--   Let $k \in \mathbb R$ and $f : \mathbb R \to \mathbb R$. Then $f$ is $k$-convex in the sense of Definition 2.2 (Porteus's form),
--   $$f\big((1-\lambda)x_0 + \lambda x_1\big) \le (1-\lambda) f(x_0) + \lambda f(x_1) + \lambda k \quad\text{for all } x_0 \le x_1,\ \lambda \in [0,1],$$
--   if and only if it is $k$-convex in the sense of Definition 2.1 (Bertsekas's form),
--   $$k + f(z + y) \ge f(y) + \frac{z}{b}\big(f(y) - f(y - b)\big) \quad\text{for all } z \ge 0,\ b > 0,\ y \in \mathbb R.$$
--
--   The paper states this equivalence when it introduces Definition 2.2 and works with whichever form is convenient: Lemma 1 is quoted in the form (4), while the induction step of Theorem 3.1 verifies the form (5).
--
--   **Formalization Note.** Both sides are stated for every real $k$; each forces $k \ge 0$ (take $\lambda = 1$, respectively $z = 0$), so the equivalence also holds for $k < 0$, where both sides are false.
-- source:
--   Chen, Simchi-Levi, Coordinating Inventory Control and Pricing Strategies with Random Demand and Fixed Ordering Cost: The Finite Horizon Case, Operations Research 52(6) (2004), p. 889, §2, Definitions 2.1–2.2

import Mathlib
import Definitions.Def_BertsekasKConvex
import Definitions.Def_ChenSimchiLevi_Additive_KConvexPorteus

namespace ChenSimchiLevi.Additive

/-- Chen–Simchi-Levi (2004), §2, p. 889: Definition 2.2 (Porteus's form (5)) of `k`-convexity is
equivalent to Definition 2.1 (Bertsekas's form (4)). -/
theorem kconvex_def22_iff_def21 (k : ℝ) (f : ℝ → ℝ) :
    KConvexPorteus k f ↔ BertsekasKConvex k f := by sorry

end ChenSimchiLevi.Additive
