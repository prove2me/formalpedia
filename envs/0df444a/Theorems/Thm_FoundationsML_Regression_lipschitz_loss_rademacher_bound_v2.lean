-- Prove2me | Theorems.Thm_FoundationsML_Regression_lipschitz_loss_rademacher_bound_v2
-- name    : FoundationsML.Regression.lipschitz_loss_rademacher_bound_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:18:56.975001+00:00
-- url     : https://prove2.me/theorems/e7d9c627-f012-459c-86e0-7399e6f4c902
-- title:
--   Proposition 11.2 — Rademacher complexity of $\mu$-Lipschitz loss functions (bounded $H$)
-- statement:
--   **Statement (Proposition 11.2, p. 269, PDF p. 286).** Let $L$ be non-negative, bounded by $M>0$, and $\mu$-Lipschitz in its first argument, and $H$ a family of real-valued functions mapping into a bounded interval $[a,b]$ (Definition 3.1's standing assumption). Then, for any sample $S$, the empirical Rademacher complexity of $G=\{(x,y)\mapsto L(h(x),y):h\in H\}$ satisfies $\hat R_S(G)\le\mu\hat R_S(H)$.
--
--   **Formalization Note.** The retired version used the retired `EmpiricalRademacherComplexity`, whose real supremum `⨆ g ∈ G, …` returns the junk value $0$ for an unbounded family, so an unbounded $H$ had complexity $0$ while the bounded $G$ did not (the accepted disproof). The corrected `EmpiricalRademacherComplexity` (`_v2`, supremum over exactly the family) is used and Definition 3.1's boundedness of $H$ is explicit; for unbounded $H$ the book's right-hand side is $+\infty$. `hLlip` is Lipschitzness in the first argument only, with the label $y'$ fixed.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 269, Proposition 11.2 (PDF p. 286)

import Mathlib
import Definitions.Def_FoundationsML_Regression_EmpiricalRademacherComplexity_v2
import Definitions.Def_FoundationsML_Regression_LossComposedFamily

namespace FoundationsML.Regression

/-- Proposition 11.2 (Rademacher complexity of µ-Lipschitz loss functions; Mohri,
Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 269,
PDF p. 286). Let `L` be a non-negative loss bounded by `M > 0` that is `µ`-Lipschitz in its
first argument, and `H` a (bounded, as Definition 3.1 requires) family of real-valued
functions. Then, for any sample `S`, the empirical Rademacher complexity of the loss-composed
family `G = {(x,y) ↦ L(h(x),y) : h ∈ H}` satisfies `R̂_S(G) ≤ µ R̂_S(H)`.

**Formalization Note.** Replaces `lipschitz_loss_rademacher_bound`, which used the retired
`EmpiricalRademacherComplexity` whose supremum `⨆ g ∈ G, …` on `ℝ` returns the junk value `0`
for an unbounded family, so an unbounded `H` had complexity `0` while the bounded `G` did not
(the disproof). The corrected `EmpiricalRademacherComplexity` (`_v2`, supremum over exactly
the family) is used, and Definition 3.1's standing assumption that `H` maps into a bounded
interval `[a,b]` is explicit (`hHb`); for unbounded `H` the book's right-hand side is `+∞`.
`hLlip` is Lipschitzness in the first argument only, with `y'` fixed. -/
theorem lipschitz_loss_rademacher_bound_v2
    {X : Type*} {m : ℕ}
    (L : ℝ → ℝ → ℝ) (M μ : ℝ) (hM : 0 < M) (hLnn : ∀ y y', 0 ≤ L y y')
    (hLb : ∀ y y', L y y' ≤ M) (hμ : 0 < μ)
    (hLlip : ∀ y' y1 y2, |L y1 y' - L y2 y'| ≤ μ * |y1 - y2|)
    (H : Set (X → ℝ)) (hHb : ∃ a b : ℝ, ∀ h ∈ H, ∀ x, h x ∈ Set.Icc a b)
    (S : Fin m → X × ℝ) :
    EmpiricalRademacherComplexity (LossComposedFamily L H) S ≤
      μ * EmpiricalRademacherComplexity H (fun i => (S i).1) := by sorry

end FoundationsML.Regression
